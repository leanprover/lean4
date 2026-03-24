// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp
// Imports: public import Lean.Compiler.LCNF.ReduceJpArity public import Lean.Compiler.LCNF.Simp.Basic public import Lean.Compiler.LCNF.Simp.FunDeclInfo public import Lean.Compiler.LCNF.Simp.JpCases public import Lean.Compiler.LCNF.Simp.Config public import Lean.Compiler.LCNF.Simp.InlineCandidate public import Lean.Compiler.LCNF.Simp.SimpM public import Lean.Compiler.LCNF.Simp.Main public import Lean.Compiler.LCNF.Simp.InlineProj public import Lean.Compiler.LCNF.Simp.DefaultAlt public import Lean.Compiler.LCNF.Simp.SimpValue public import Lean.Compiler.LCNF.Simp.Used
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
lean_object* l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_reduceJpArity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_size(uint8_t, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_applyRenaming(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ppCode(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ppDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedPass;
lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(lean_object*, uint8_t, uint8_t, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__2;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__3;
static const lean_string_object l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__4 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__4_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__5 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "stat"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(5, 122, 96, 221, 209, 205, 68, 156)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(25, 138, 225, 205, 253, 207, 170, 22)}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = ", size: "};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ", # visited: "};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = ", # inline: "};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = ", # inline local: "};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "new"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " :=\n"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "step"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(5, 122, 96, 221, 209, 205, 68, 156)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(129, 254, 255, 237, 198, 170, 92, 26)}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "inline"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "info"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(5, 122, 96, 221, 209, 205, 68, 156)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17_value),LEAN_SCALAR_PTR_LITERAL(186, 182, 14, 42, 67, 101, 187, 98)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18_value),LEAN_SCALAR_PTR_LITERAL(102, 156, 22, 89, 74, 242, 244, 96)}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_simp___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(195, 61, 75, 186, 44, 210, 52, 194)}};
static const lean_object* l_Lean_Compiler_LCNF_simp___lam__1___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_simp___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___lam__1(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(5, 122, 96, 221, 209, 205, 68, 156)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(65, 104, 221, 94, 203, 189, 176, 167)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(100, 132, 133, 172, 235, 219, 4, 203)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(197, 110, 72, 179, 97, 243, 53, 118)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(131, 3, 255, 150, 103, 178, 140, 69)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(142, 204, 178, 138, 220, 209, 109, 127)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(35, 50, 18, 60, 6, 246, 183, 66)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(22, 41, 223, 173, 54, 220, 153, 106)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(191, 25, 17, 59, 203, 138, 75, 112)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 69, 196, 80, 62, 232, 177, 169)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(84, 26, 102, 137, 178, 105, 245, 114)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(232, 0, 19, 243, 30, 245, 70, 97)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1672504145) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(72, 138, 113, 209, 207, 47, 220, 70)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 108, 170, 7, 92, 109, 147, 19)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 198, 6, 36, 160, 118, 14, 150)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(2, 47, 254, 130, 93, 85, 156, 37)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(5, 122, 96, 221, 209, 205, 68, 156)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(129, 254, 255, 237, 198, 170, 92, 26)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(92, 168, 59, 39, 78, 228, 188, 146)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(lean_object* v_cls_4_, lean_object* v___y_5_){
_start:
{
lean_object* v_options_7_; uint8_t v_hasTrace_8_; 
v_options_7_ = lean_ctor_get(v___y_5_, 2);
v_hasTrace_8_ = lean_ctor_get_uint8(v_options_7_, sizeof(void*)*1);
if (v_hasTrace_8_ == 0)
{
lean_object* v___x_9_; lean_object* v___x_10_; 
lean_dec(v_cls_4_);
v___x_9_ = lean_box(v_hasTrace_8_);
v___x_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
return v___x_10_;
}
else
{
lean_object* v_inheritedTraceOptions_11_; lean_object* v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_inheritedTraceOptions_11_ = lean_ctor_get(v___y_5_, 13);
v___x_12_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__1));
v___x_13_ = l_Lean_Name_append(v___x_12_, v_cls_4_);
v___x_14_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_11_, v_options_7_, v___x_13_);
lean_dec(v___x_13_);
v___x_15_ = lean_box(v___x_14_);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___boxed(lean_object* v_cls_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v_cls_17_, v___y_18_);
lean_dec_ref(v___y_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0(lean_object* v_cls_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v_cls_21_, v___y_27_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___boxed(lean_object* v_cls_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0(v_cls_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_);
lean_dec(v___y_38_);
lean_dec_ref(v___y_37_);
lean_dec(v___y_36_);
lean_dec_ref(v___y_35_);
lean_dec_ref(v___y_34_);
lean_dec(v___y_33_);
lean_dec_ref(v___y_32_);
return v_res_40_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_41_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__0);
v___x_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
return v___x_43_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__1);
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
lean_ctor_set(v___x_46_, 1, v___x_45_);
lean_ctor_set(v___x_46_, 2, v___x_45_);
lean_ctor_set(v___x_46_, 3, v___x_44_);
lean_ctor_set(v___x_46_, 4, v___x_44_);
lean_ctor_set(v___x_46_, 5, v___x_44_);
lean_ctor_set(v___x_46_, 6, v___x_44_);
lean_ctor_set(v___x_46_, 7, v___x_44_);
lean_ctor_set(v___x_46_, 8, v___x_44_);
return v___x_46_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_47_; double v___x_48_; 
v___x_47_ = lean_unsigned_to_nat(0u);
v___x_48_ = lean_float_of_nat(v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(lean_object* v_cls_52_, lean_object* v_msg_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_options_59_; lean_object* v_ref_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v_options_59_ = lean_ctor_get(v___y_56_, 2);
v_ref_60_ = lean_ctor_get(v___y_56_, 5);
v___x_61_ = lean_st_ref_get(v___y_57_);
v___x_62_ = lean_st_ref_get(v___y_55_);
v___x_63_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_54_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v_a_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_122_; 
v_a_64_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_122_ == 0)
{
v___x_66_ = v___x_63_;
v_isShared_67_ = v_isSharedCheck_122_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_a_64_);
lean_dec(v___x_63_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_122_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v_env_68_; lean_object* v_lctx_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_120_; 
v_env_68_ = lean_ctor_get(v___x_61_, 0);
lean_inc_ref(v_env_68_);
lean_dec(v___x_61_);
v_lctx_69_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_120_ == 0)
{
lean_object* v_unused_121_; 
v_unused_121_ = lean_ctor_get(v___x_62_, 1);
lean_dec(v_unused_121_);
v___x_71_ = v___x_62_;
v_isShared_72_ = v_isSharedCheck_120_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_lctx_69_);
lean_dec(v___x_62_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_120_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v_traceState_75_; lean_object* v_env_76_; lean_object* v_nextMacroScope_77_; lean_object* v_ngen_78_; lean_object* v_auxDeclNGen_79_; lean_object* v_cache_80_; lean_object* v_messages_81_; lean_object* v_infoState_82_; lean_object* v_snapshotTasks_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_119_; 
v___x_73_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__2);
v___x_74_ = lean_st_ref_take(v___y_57_);
v_traceState_75_ = lean_ctor_get(v___x_74_, 4);
v_env_76_ = lean_ctor_get(v___x_74_, 0);
v_nextMacroScope_77_ = lean_ctor_get(v___x_74_, 1);
v_ngen_78_ = lean_ctor_get(v___x_74_, 2);
v_auxDeclNGen_79_ = lean_ctor_get(v___x_74_, 3);
v_cache_80_ = lean_ctor_get(v___x_74_, 5);
v_messages_81_ = lean_ctor_get(v___x_74_, 6);
v_infoState_82_ = lean_ctor_get(v___x_74_, 7);
v_snapshotTasks_83_ = lean_ctor_get(v___x_74_, 8);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_119_ == 0)
{
v___x_85_ = v___x_74_;
v_isShared_86_ = v_isSharedCheck_119_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_snapshotTasks_83_);
lean_inc(v_infoState_82_);
lean_inc(v_messages_81_);
lean_inc(v_cache_80_);
lean_inc(v_traceState_75_);
lean_inc(v_auxDeclNGen_79_);
lean_inc(v_ngen_78_);
lean_inc(v_nextMacroScope_77_);
lean_inc(v_env_76_);
lean_dec(v___x_74_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_119_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
uint64_t v_tid_87_; lean_object* v_traces_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_118_; 
v_tid_87_ = lean_ctor_get_uint64(v_traceState_75_, sizeof(void*)*1);
v_traces_88_ = lean_ctor_get(v_traceState_75_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v_traceState_75_);
if (v_isSharedCheck_118_ == 0)
{
v___x_90_ = v_traceState_75_;
v_isShared_91_ = v_isSharedCheck_118_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_traces_88_);
lean_dec(v_traceState_75_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_118_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
uint8_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_96_; 
v___x_92_ = lean_unbox(v_a_64_);
lean_dec(v_a_64_);
v___x_93_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_69_, v___x_92_);
lean_dec_ref(v_lctx_69_);
lean_inc_ref(v_options_59_);
v___x_94_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_94_, 0, v_env_68_);
lean_ctor_set(v___x_94_, 1, v___x_73_);
lean_ctor_set(v___x_94_, 2, v___x_93_);
lean_ctor_set(v___x_94_, 3, v_options_59_);
if (v_isShared_72_ == 0)
{
lean_ctor_set_tag(v___x_71_, 3);
lean_ctor_set(v___x_71_, 1, v_msg_53_);
lean_ctor_set(v___x_71_, 0, v___x_94_);
v___x_96_ = v___x_71_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_94_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v_msg_53_);
v___x_96_ = v_reuseFailAlloc_117_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
lean_object* v___x_97_; double v___x_98_; uint8_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_107_; 
v___x_97_ = lean_box(0);
v___x_98_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__3);
v___x_99_ = 0;
v___x_100_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__4));
v___x_101_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_101_, 0, v_cls_52_);
lean_ctor_set(v___x_101_, 1, v___x_97_);
lean_ctor_set(v___x_101_, 2, v___x_100_);
lean_ctor_set_float(v___x_101_, sizeof(void*)*3, v___x_98_);
lean_ctor_set_float(v___x_101_, sizeof(void*)*3 + 8, v___x_98_);
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*3 + 16, v___x_99_);
v___x_102_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__5));
v___x_103_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_103_, 0, v___x_101_);
lean_ctor_set(v___x_103_, 1, v___x_96_);
lean_ctor_set(v___x_103_, 2, v___x_102_);
lean_inc(v_ref_60_);
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v_ref_60_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = l_Lean_PersistentArray_push___redArg(v_traces_88_, v___x_104_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 0, v___x_105_);
v___x_107_ = v___x_90_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_105_);
lean_ctor_set_uint64(v_reuseFailAlloc_116_, sizeof(void*)*1, v_tid_87_);
v___x_107_ = v_reuseFailAlloc_116_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
lean_object* v___x_109_; 
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 4, v___x_107_);
v___x_109_ = v___x_85_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_env_76_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v_nextMacroScope_77_);
lean_ctor_set(v_reuseFailAlloc_115_, 2, v_ngen_78_);
lean_ctor_set(v_reuseFailAlloc_115_, 3, v_auxDeclNGen_79_);
lean_ctor_set(v_reuseFailAlloc_115_, 4, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_115_, 5, v_cache_80_);
lean_ctor_set(v_reuseFailAlloc_115_, 6, v_messages_81_);
lean_ctor_set(v_reuseFailAlloc_115_, 7, v_infoState_82_);
lean_ctor_set(v_reuseFailAlloc_115_, 8, v_snapshotTasks_83_);
v___x_109_ = v_reuseFailAlloc_115_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_113_; 
v___x_110_ = lean_st_ref_set(v___y_57_, v___x_109_);
v___x_111_ = lean_box(0);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 0, v___x_111_);
v___x_113_ = v___x_66_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
lean_dec(v___x_62_);
lean_dec(v___x_61_);
lean_dec_ref(v_msg_53_);
lean_dec(v_cls_52_);
v_a_123_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v___x_63_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_63_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_123_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___boxed(lean_object* v_cls_131_, lean_object* v_msg_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(v_cls_131_, v_msg_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1(lean_object* v_cls_139_, lean_object* v_msg_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(v_cls_139_, v_msg_140_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___boxed(lean_object* v_cls_150_, lean_object* v_msg_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1(v_cls_150_, v_msg_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec_ref(v___y_154_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
return v_res_160_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4));
v___x_170_ = l_Lean_stringToMessageData(v___x_169_);
return v___x_170_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6));
v___x_173_ = l_Lean_stringToMessageData(v___x_172_);
return v___x_173_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8));
v___x_176_ = l_Lean_stringToMessageData(v___x_175_);
return v___x_176_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10));
v___x_179_ = l_Lean_stringToMessageData(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13));
v___x_183_ = l_Lean_stringToMessageData(v___x_182_);
return v___x_183_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20));
v___x_198_ = l_Lean_stringToMessageData(v___x_197_);
return v___x_198_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_unsigned_to_nat(2u);
v___x_200_ = lean_nat_to_int(v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f(lean_object* v_decl_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_toSignature_210_; lean_object* v_value_211_; uint8_t v_recursive_212_; lean_object* v_inlineAttr_x3f_213_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_218_; lean_object* v___y_219_; lean_object* v___y_220_; 
v_toSignature_210_ = lean_ctor_get(v_decl_201_, 0);
lean_inc_ref(v_toSignature_210_);
v_value_211_ = lean_ctor_get(v_decl_201_, 1);
lean_inc_ref(v_value_211_);
v_recursive_212_ = lean_ctor_get_uint8(v_decl_201_, sizeof(void*)*3);
v_inlineAttr_x3f_213_ = lean_ctor_get(v_decl_201_, 2);
lean_inc(v_inlineAttr_x3f_213_);
if (lean_obj_tag(v_value_211_) == 0)
{
lean_object* v_code_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_462_; 
v_code_274_ = lean_ctor_get(v_value_211_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v_value_211_);
if (v_isSharedCheck_462_ == 0)
{
v___x_276_ = v_value_211_;
v_isShared_277_ = v_isSharedCheck_462_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_code_274_);
lean_dec(v_value_211_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_462_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
uint8_t v___x_278_; lean_object* v___x_279_; 
v___x_278_ = 0;
lean_inc_ref(v_code_274_);
v___x_279_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(v_code_274_, v___x_278_, v_a_203_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; uint8_t v___y_287_; lean_object* v___y_337_; uint8_t v___y_338_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v_a_423_; uint8_t v___x_424_; 
lean_dec_ref(v___x_279_);
v___x_280_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0));
v___x_281_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1));
v___x_421_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19));
v___x_422_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v___x_421_, v_a_207_);
v_a_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_a_423_);
lean_dec_ref(v___x_422_);
v___x_424_ = lean_unbox(v_a_423_);
lean_dec(v_a_423_);
if (v___x_424_ == 0)
{
goto v___jp_394_;
}
else
{
lean_object* v___x_425_; lean_object* v_funDeclInfoMap_426_; lean_object* v___x_427_; 
v___x_425_ = lean_st_ref_get(v_a_203_);
v_funDeclInfoMap_426_ = lean_ctor_get(v___x_425_, 3);
lean_inc_ref(v_funDeclInfoMap_426_);
lean_dec(v___x_425_);
v___x_427_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(v_funDeclInfoMap_426_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
lean_dec_ref(v_funDeclInfoMap_426_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v_name_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_a_428_);
lean_dec_ref(v___x_427_);
v_name_429_ = lean_ctor_get(v_toSignature_210_, 0);
lean_inc(v_name_429_);
v___x_430_ = l_Lean_MessageData_ofName(v_name_429_);
v___x_431_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21);
v___x_432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_430_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22);
v___x_434_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
lean_ctor_set(v___x_434_, 1, v_a_428_);
v___x_435_ = l_Lean_MessageData_ofFormat(v___x_434_);
v___x_436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_432_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
v___x_437_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(v___x_421_, v___x_436_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_dec_ref(v___x_437_);
goto v___jp_394_;
}
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
lean_del_object(v___x_276_);
lean_dec_ref(v_code_274_);
lean_dec(v_inlineAttr_x3f_213_);
lean_dec_ref(v_toSignature_210_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec_ref(v_decl_201_);
v_a_438_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_437_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_del_object(v___x_276_);
lean_dec_ref(v_code_274_);
lean_dec(v_inlineAttr_x3f_213_);
lean_dec_ref(v_toSignature_210_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec_ref(v_decl_201_);
v_a_446_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_427_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_427_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
v___jp_282_:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_335_; 
v___x_288_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3));
v___x_289_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v___x_288_, v_a_207_);
v_a_290_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_335_ == 0)
{
v___x_292_ = v___x_289_;
v_isShared_293_ = v_isSharedCheck_335_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_289_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_335_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
uint8_t v___x_294_; 
v___x_294_ = lean_unbox(v_a_290_);
lean_dec(v_a_290_);
if (v___x_294_ == 0)
{
lean_del_object(v___x_292_);
lean_dec(v___y_286_);
lean_dec(v___y_284_);
lean_dec(v___y_283_);
lean_del_object(v___x_276_);
v___y_215_ = v___y_285_;
v___y_216_ = v_a_203_;
v___y_217_ = v_a_205_;
v___y_218_ = v_a_206_;
v___y_219_ = v_a_207_;
v___y_220_ = v_a_208_;
goto v___jp_214_;
}
else
{
lean_object* v_name_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_302_; 
v_name_295_ = lean_ctor_get(v_toSignature_210_, 0);
lean_inc(v_name_295_);
v___x_296_ = l_Lean_MessageData_ofName(v_name_295_);
v___x_297_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5);
v___x_298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = l_Lean_Compiler_LCNF_Code_size(v___y_287_, v___y_285_);
v___x_300_ = l_Nat_reprFast(v___x_299_);
if (v_isShared_293_ == 0)
{
lean_ctor_set_tag(v___x_292_, 3);
lean_ctor_set(v___x_292_, 0, v___x_300_);
v___x_302_ = v___x_292_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_300_);
v___x_302_ = v_reuseFailAlloc_334_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_303_ = l_Lean_MessageData_ofFormat(v___x_302_);
v___x_304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_298_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7);
v___x_306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_304_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = l_Nat_reprFast(v___y_284_);
if (v_isShared_277_ == 0)
{
lean_ctor_set_tag(v___x_276_, 3);
lean_ctor_set(v___x_276_, 0, v___x_307_);
v___x_309_ = v___x_276_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_307_);
v___x_309_ = v_reuseFailAlloc_333_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_310_ = l_Lean_MessageData_ofFormat(v___x_309_);
v___x_311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_306_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9);
v___x_313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_311_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
v___x_314_ = l_Nat_reprFast(v___y_286_);
v___x_315_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
v___x_316_ = l_Lean_MessageData_ofFormat(v___x_315_);
v___x_317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_313_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11);
v___x_319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_317_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = l_Nat_reprFast(v___y_283_);
v___x_321_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
v___x_322_ = l_Lean_MessageData_ofFormat(v___x_321_);
v___x_323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_319_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(v___x_288_, v___x_323_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_dec_ref(v___x_324_);
v___y_215_ = v___y_285_;
v___y_216_ = v_a_203_;
v___y_217_ = v_a_205_;
v___y_218_ = v_a_206_;
v___y_219_ = v_a_207_;
v___y_220_ = v_a_208_;
goto v___jp_214_;
}
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_dec_ref(v___y_285_);
lean_dec(v_inlineAttr_x3f_213_);
lean_dec_ref(v_toSignature_210_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec(v_a_203_);
v_a_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
}
}
}
v___jp_336_:
{
lean_object* v___x_339_; 
lean_inc(v_a_208_);
lean_inc_ref(v_a_207_);
lean_inc(v_a_206_);
lean_inc_ref(v_a_205_);
lean_inc(v_a_203_);
v___x_339_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_274_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_341_; lean_object* v_binderRenaming_342_; lean_object* v_visited_343_; lean_object* v_inline_344_; lean_object* v_inlineLocal_345_; lean_object* v___x_346_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
lean_dec_ref(v___x_339_);
v___x_341_ = lean_st_ref_get(v_a_203_);
v_binderRenaming_342_ = lean_ctor_get(v___x_341_, 2);
lean_inc(v_binderRenaming_342_);
v_visited_343_ = lean_ctor_get(v___x_341_, 4);
lean_inc(v_visited_343_);
v_inline_344_ = lean_ctor_get(v___x_341_, 5);
lean_inc(v_inline_344_);
v_inlineLocal_345_ = lean_ctor_get(v___x_341_, 6);
lean_inc(v_inlineLocal_345_);
lean_dec(v___x_341_);
v___x_346_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v___y_338_, v_a_340_, v_binderRenaming_342_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
lean_dec(v_binderRenaming_342_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v_a_351_; uint8_t v___x_352_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_a_347_);
lean_dec_ref(v___x_346_);
v___x_348_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12));
v___x_349_ = l_Lean_Name_mkStr4(v___x_280_, v___x_281_, v___y_337_, v___x_348_);
lean_inc(v___x_349_);
v___x_350_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v___x_349_, v_a_207_);
v_a_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_a_351_);
lean_dec_ref(v___x_350_);
v___x_352_ = lean_unbox(v_a_351_);
lean_dec(v_a_351_);
if (v___x_352_ == 0)
{
lean_dec(v___x_349_);
v___y_283_ = v_inlineLocal_345_;
v___y_284_ = v_visited_343_;
v___y_285_ = v_a_347_;
v___y_286_ = v_inline_344_;
v___y_287_ = v___y_338_;
goto v___jp_282_;
}
else
{
lean_object* v___x_353_; 
lean_inc(v_a_208_);
lean_inc_ref(v_a_207_);
lean_inc(v_a_206_);
lean_inc_ref(v_a_205_);
lean_inc(v_a_347_);
v___x_353_ = l_Lean_Compiler_LCNF_ppCode(v___y_338_, v_a_347_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; lean_object* v_name_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_a_354_);
lean_dec_ref(v___x_353_);
v_name_355_ = lean_ctor_get(v_toSignature_210_, 0);
lean_inc(v_name_355_);
v___x_356_ = l_Lean_MessageData_ofName(v_name_355_);
v___x_357_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14);
v___x_358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_356_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
v___x_359_ = l_Lean_MessageData_ofFormat(v_a_354_);
v___x_360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_358_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(v___x_349_, v___x_360_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_dec_ref(v___x_361_);
v___y_283_ = v_inlineLocal_345_;
v___y_284_ = v_visited_343_;
v___y_285_ = v_a_347_;
v___y_286_ = v_inline_344_;
v___y_287_ = v___y_338_;
goto v___jp_282_;
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec(v_a_347_);
lean_dec(v_inlineLocal_345_);
lean_dec(v_inline_344_);
lean_dec(v_visited_343_);
lean_del_object(v___x_276_);
lean_dec(v_inlineAttr_x3f_213_);
lean_dec_ref(v_toSignature_210_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec(v_a_203_);
v_a_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_361_);
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
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
lean_dec(v___x_349_);
lean_dec(v_a_347_);
lean_dec(v_inlineLocal_345_);
lean_dec(v_inline_344_);
lean_dec(v_visited_343_);
lean_del_object(v___x_276_);
lean_dec(v_inlineAttr_x3f_213_);
lean_dec_ref(v_toSignature_210_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec(v_a_203_);
v_a_370_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_353_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_353_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
else
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_385_; 
lean_dec(v_inlineLocal_345_);
lean_dec(v_inline_344_);
lean_dec(v_visited_343_);
lean_dec_ref(v___y_337_);
lean_del_object(v___x_276_);
lean_dec(v_inlineAttr_x3f_213_);
lean_dec_ref(v_toSignature_210_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec(v_a_203_);
v_a_378_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_385_ == 0)
{
v___x_380_ = v___x_346_;
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_346_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_383_; 
if (v_isShared_381_ == 0)
{
v___x_383_ = v___x_380_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_a_378_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
else
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
lean_dec_ref(v___y_337_);
lean_del_object(v___x_276_);
lean_dec(v_inlineAttr_x3f_213_);
lean_dec_ref(v_toSignature_210_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec(v_a_203_);
v_a_386_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_339_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_339_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
v___jp_394_:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v_a_398_; uint8_t v___x_399_; uint8_t v___x_400_; 
v___x_395_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15));
v___x_396_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16));
v___x_397_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v___x_396_, v_a_207_);
v_a_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_a_398_);
lean_dec_ref(v___x_397_);
v___x_399_ = 0;
v___x_400_ = lean_unbox(v_a_398_);
lean_dec(v_a_398_);
if (v___x_400_ == 0)
{
lean_dec_ref(v_decl_201_);
v___y_337_ = v___x_395_;
v___y_338_ = v___x_399_;
goto v___jp_336_;
}
else
{
lean_object* v___x_401_; 
lean_inc(v_a_208_);
lean_inc_ref(v_a_207_);
lean_inc(v_a_206_);
lean_inc_ref(v_a_205_);
v___x_401_ = l_Lean_Compiler_LCNF_ppDecl(v___x_399_, v_decl_201_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_a_402_);
lean_dec_ref(v___x_401_);
v___x_403_ = l_Lean_MessageData_ofFormat(v_a_402_);
v___x_404_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(v___x_396_, v___x_403_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_dec_ref(v___x_404_);
v___y_337_ = v___x_395_;
v___y_338_ = v___x_399_;
goto v___jp_336_;
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_del_object(v___x_276_);
lean_dec_ref(v_code_274_);
lean_dec(v_inlineAttr_x3f_213_);
lean_dec_ref(v_toSignature_210_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
v_a_405_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_404_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_404_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_del_object(v___x_276_);
lean_dec_ref(v_code_274_);
lean_dec(v_inlineAttr_x3f_213_);
lean_dec_ref(v_toSignature_210_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
v_a_413_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_401_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_401_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
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
else
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
lean_del_object(v___x_276_);
lean_dec_ref(v_code_274_);
lean_dec(v_inlineAttr_x3f_213_);
lean_dec_ref(v_toSignature_210_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec_ref(v_decl_201_);
v_a_454_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v___x_279_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_279_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_454_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
}
else
{
lean_object* v___x_463_; lean_object* v___x_464_; 
lean_dec(v_inlineAttr_x3f_213_);
lean_dec_ref(v_value_211_);
lean_dec_ref(v_toSignature_210_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec_ref(v_decl_201_);
v___x_463_ = lean_box(0);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
v___jp_214_:
{
lean_object* v___x_221_; 
lean_inc(v___y_220_);
lean_inc_ref(v___y_219_);
lean_inc(v___y_218_);
lean_inc_ref(v___y_217_);
lean_inc_ref(v___y_215_);
v___x_221_ = l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(v___y_215_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_265_; 
v_a_222_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_265_ == 0)
{
v___x_224_ = v___x_221_;
v_isShared_225_ = v_isSharedCheck_265_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_221_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_265_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
if (lean_obj_tag(v_a_222_) == 1)
{
lean_object* v_val_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_252_; 
lean_del_object(v___x_224_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
v_val_226_ = lean_ctor_get(v_a_222_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v_a_222_);
if (v_isSharedCheck_252_ == 0)
{
v___x_228_ = v_a_222_;
v_isShared_229_ = v_isSharedCheck_252_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_val_226_);
lean_dec(v_a_222_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_252_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_230_, 0, v_val_226_);
v___x_231_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_231_, 0, v_toSignature_210_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
lean_ctor_set(v___x_231_, 2, v_inlineAttr_x3f_213_);
lean_ctor_set_uint8(v___x_231_, sizeof(void*)*3, v_recursive_212_);
v___x_232_ = l_Lean_Compiler_LCNF_Decl_reduceJpArity(v___x_231_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_243_; 
v_a_233_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_243_ == 0)
{
v___x_235_ = v___x_232_;
v_isShared_236_ = v_isSharedCheck_243_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_232_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_243_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v_a_233_);
v___x_238_ = v___x_228_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_233_);
v___x_238_ = v_reuseFailAlloc_242_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_240_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v___x_238_);
v___x_240_ = v___x_235_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_238_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
lean_del_object(v___x_228_);
v_a_244_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_232_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_232_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
else
{
lean_object* v___x_253_; uint8_t v_simplified_254_; 
lean_dec(v_a_222_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
v___x_253_ = lean_st_ref_get(v___y_216_);
lean_dec(v___y_216_);
v_simplified_254_ = lean_ctor_get_uint8(v___x_253_, sizeof(void*)*7);
lean_dec(v___x_253_);
if (v_simplified_254_ == 0)
{
lean_object* v___x_255_; lean_object* v___x_257_; 
lean_dec_ref(v___y_215_);
lean_dec(v_inlineAttr_x3f_213_);
lean_dec_ref(v_toSignature_210_);
v___x_255_ = lean_box(0);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_255_);
v___x_257_ = v___x_224_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_255_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
else
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v___y_215_);
v___x_260_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_260_, 0, v_toSignature_210_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
lean_ctor_set(v___x_260_, 2, v_inlineAttr_x3f_213_);
lean_ctor_set_uint8(v___x_260_, sizeof(void*)*3, v_recursive_212_);
v___x_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_261_);
v___x_263_ = v___x_224_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
}
else
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v_inlineAttr_x3f_213_);
lean_dec_ref(v_toSignature_210_);
v_a_266_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_273_ == 0)
{
v___x_268_ = v___x_221_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_221_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___boxed(lean_object* v_decl_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Compiler_LCNF_Decl_simp_x3f(v_decl_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_);
return v_res_474_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_475_ = lean_box(0);
v___x_476_ = lean_unsigned_to_nat(16u);
v___x_477_ = lean_mk_array(v___x_476_, v___x_475_);
return v___x_477_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0, &l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0);
v___x_479_ = lean_unsigned_to_nat(0u);
v___x_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
lean_ctor_set(v___x_480_, 1, v___x_478_);
return v___x_480_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2(void){
_start:
{
lean_object* v___x_481_; uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_481_ = lean_unsigned_to_nat(0u);
v___x_482_ = 0;
v___x_483_ = lean_box(1);
v___x_484_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_485_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1, &l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1);
v___x_486_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v___x_484_);
lean_ctor_set(v___x_486_, 2, v___x_483_);
lean_ctor_set(v___x_486_, 3, v___x_485_);
lean_ctor_set(v___x_486_, 4, v___x_481_);
lean_ctor_set(v___x_486_, 5, v___x_481_);
lean_ctor_set(v___x_486_, 6, v___x_481_);
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*7, v___x_482_);
return v___x_486_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__1);
v___x_488_ = lean_box(1);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v___x_487_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go(lean_object* v_decl_490_, lean_object* v_config_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v_toSignature_499_; lean_object* v_name_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_497_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2, &l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2_once, _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2);
v___x_498_ = lean_st_mk_ref(v___x_497_);
v_toSignature_499_ = lean_ctor_get(v_decl_490_, 0);
v_name_500_ = lean_ctor_get(v_toSignature_499_, 0);
v___x_501_ = lean_box(0);
v___x_502_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__1);
lean_inc_ref(v_config_491_);
lean_inc(v_name_500_);
v___x_503_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_503_, 0, v_name_500_);
lean_ctor_set(v___x_503_, 1, v_config_491_);
lean_ctor_set(v___x_503_, 2, v___x_501_);
lean_ctor_set(v___x_503_, 3, v___x_502_);
v___x_504_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3, &l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3);
lean_inc(v_a_495_);
lean_inc_ref(v_a_494_);
lean_inc(v_a_493_);
lean_inc_ref(v_a_492_);
lean_inc(v___x_498_);
lean_inc_ref(v_decl_490_);
v___x_505_ = l_Lean_Compiler_LCNF_Decl_simp_x3f(v_decl_490_, v___x_503_, v___x_498_, v___x_504_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_516_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_516_ == 0)
{
v___x_508_ = v___x_505_;
v_isShared_509_ = v_isSharedCheck_516_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_516_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; 
v___x_510_ = lean_st_ref_get(v___x_498_);
lean_dec(v___x_498_);
lean_dec(v___x_510_);
if (lean_obj_tag(v_a_506_) == 1)
{
lean_object* v_val_511_; 
lean_del_object(v___x_508_);
lean_dec_ref(v_decl_490_);
v_val_511_ = lean_ctor_get(v_a_506_, 0);
lean_inc(v_val_511_);
lean_dec_ref(v_a_506_);
v_decl_490_ = v_val_511_;
goto _start;
}
else
{
lean_object* v___x_514_; 
lean_dec(v_a_506_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec_ref(v_config_491_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v_decl_490_);
v___x_514_ = v___x_508_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_decl_490_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_dec(v___x_498_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec_ref(v_config_491_);
lean_dec_ref(v_decl_490_);
v_a_517_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_505_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_505_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___boxed(lean_object* v_decl_525_, lean_object* v_config_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go(v_decl_525_, v_config_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp(lean_object* v_decl_533_, lean_object* v_config_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_){
_start:
{
lean_object* v___x_540_; 
lean_inc_ref(v_decl_533_);
v___x_540_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(v_decl_533_, v_a_537_, v_a_538_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; uint8_t v___x_542_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_a_541_);
lean_dec_ref(v___x_540_);
v___x_542_ = lean_unbox(v_a_541_);
lean_dec(v_a_541_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; 
v___x_543_ = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go(v_decl_533_, v_config_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
return v___x_543_;
}
else
{
uint8_t v_implementedBy_544_; uint8_t v_inlineDefs_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_554_; 
v_implementedBy_544_ = lean_ctor_get_uint8(v_config_534_, 2);
v_inlineDefs_545_ = lean_ctor_get_uint8(v_config_534_, 3);
v_isSharedCheck_554_ = !lean_is_exclusive(v_config_534_);
if (v_isSharedCheck_554_ == 0)
{
v___x_547_ = v_config_534_;
v_isShared_548_ = v_isSharedCheck_554_;
goto v_resetjp_546_;
}
else
{
lean_dec(v_config_534_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_554_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
uint8_t v___x_549_; lean_object* v___x_551_; 
v___x_549_ = 0;
if (v_isShared_548_ == 0)
{
v___x_551_ = v___x_547_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v_reuseFailAlloc_553_, 2, v_implementedBy_544_);
lean_ctor_set_uint8(v_reuseFailAlloc_553_, 3, v_inlineDefs_545_);
v___x_551_ = v_reuseFailAlloc_553_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; 
lean_ctor_set_uint8(v___x_551_, 0, v___x_549_);
lean_ctor_set_uint8(v___x_551_, 1, v___x_549_);
v___x_552_ = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go(v_decl_533_, v___x_551_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
return v___x_552_;
}
}
}
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec_ref(v_config_534_);
lean_dec_ref(v_decl_533_);
v_a_555_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_540_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_540_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp___boxed(lean_object* v_decl_563_, lean_object* v_config_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Compiler_LCNF_Decl_simp(v_decl_563_, v_config_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___lam__0(lean_object* v_config_571_, lean_object* v_x_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_Compiler_LCNF_Decl_simp(v_x_572_, v_config_571_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___lam__0___boxed(lean_object* v_config_579_, lean_object* v_x_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_Compiler_LCNF_simp___lam__0(v_config_579_, v_x_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___lam__1(uint8_t v_phase_589_, lean_object* v___f_590_, lean_object* v_occurrence_591_, lean_object* v_h_592_){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = ((lean_object*)(l_Lean_Compiler_LCNF_simp___lam__1___closed__0));
v___x_594_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_593_, v_phase_589_, v___f_590_, v_occurrence_591_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___lam__1___boxed(lean_object* v_phase_595_, lean_object* v___f_596_, lean_object* v_occurrence_597_, lean_object* v_h_598_){
_start:
{
uint8_t v_phase_boxed_599_; lean_object* v_res_600_; 
v_phase_boxed_599_ = lean_unbox(v_phase_595_);
v_res_600_ = l_Lean_Compiler_LCNF_simp___lam__1(v_phase_boxed_599_, v___f_596_, v_occurrence_597_, v_h_598_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp(lean_object* v_config_601_, lean_object* v_occurrence_602_, uint8_t v_phase_603_){
_start:
{
lean_object* v___f_604_; lean_object* v___x_605_; lean_object* v___f_606_; lean_object* v___x_607_; uint8_t v___x_608_; lean_object* v___x_609_; 
v___f_604_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_simp___lam__0___boxed), 7, 1);
lean_closure_set(v___f_604_, 0, v_config_601_);
v___x_605_ = lean_box(v_phase_603_);
v___f_606_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_simp___lam__1___boxed), 4, 3);
lean_closure_set(v___f_606_, 0, v___x_605_);
lean_closure_set(v___f_606_, 1, v___f_604_);
lean_closure_set(v___f_606_, 2, v_occurrence_602_);
v___x_607_ = l_Lean_Compiler_LCNF_instInhabitedPass;
v___x_608_ = 0;
v___x_609_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___x_607_, v_phase_603_, v___x_608_, v___f_606_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___boxed(lean_object* v_config_610_, lean_object* v_occurrence_611_, lean_object* v_phase_612_){
_start:
{
uint8_t v_phase_boxed_613_; lean_object* v_res_614_; 
v_phase_boxed_613_ = lean_unbox(v_phase_612_);
v_res_614_ = l_Lean_Compiler_LCNF_simp(v_config_610_, v_occurrence_611_, v_phase_boxed_613_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_689_; uint8_t v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_689_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_));
v___x_690_ = 1;
v___x_691_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_));
v___x_692_ = l_Lean_registerTraceClass(v___x_689_, v___x_690_, v___x_691_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v___x_693_; uint8_t v___x_694_; lean_object* v___x_695_; 
lean_dec_ref(v___x_692_);
v___x_693_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3));
v___x_694_ = 0;
v___x_695_ = l_Lean_registerTraceClass(v___x_693_, v___x_694_, v___x_691_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v___x_696_; lean_object* v___x_697_; 
lean_dec_ref(v___x_695_);
v___x_696_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16));
v___x_697_ = l_Lean_registerTraceClass(v___x_696_, v___x_694_, v___x_691_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; 
lean_dec_ref(v___x_697_);
v___x_698_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_));
v___x_699_ = l_Lean_registerTraceClass(v___x_698_, v___x_694_, v___x_691_);
return v___x_699_;
}
else
{
return v___x_697_;
}
}
else
{
return v___x_695_;
}
}
else
{
return v___x_692_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2____boxed(lean_object* v_a_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
return v_res_701_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_ReduceJpArity(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_JpCases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_Config(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_InlineProj(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_SimpValue(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_Used(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_ReduceJpArity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_JpCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_Used(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_Simp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_ReduceJpArity(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_Basic(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_JpCases(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_Config(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_Main(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_InlineProj(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpValue(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_Used(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_ReduceJpArity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_JpCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_Used(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Simp(builtin);
}
#ifdef __cplusplus
}
#endif

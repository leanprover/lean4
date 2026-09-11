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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_reduceJpArity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_size(uint8_t, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_applyRenaming(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ppCode(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ppDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedPass;
lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(lean_object*, uint8_t, uint8_t, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__2;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__3;
static const lean_string_object l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__4 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__4_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__5 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = ", size: "};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ", # visited: "};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = ", # inline: "};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = ", # inline local: "};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "new"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " :=\n"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "step"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(5, 122, 96, 221, 209, 205, 68, 156)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18_value),LEAN_SCALAR_PTR_LITERAL(129, 254, 255, 237, 198, 170, 92, 26)}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "inline"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "info"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(5, 122, 96, 221, 209, 205, 68, 156)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21_value),LEAN_SCALAR_PTR_LITERAL(186, 182, 14, 42, 67, 101, 187, 98)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(102, 156, 22, 89, 74, 242, 244, 96)}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__25 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__25_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__27;
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
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__5;
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
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18_value),LEAN_SCALAR_PTR_LITERAL(129, 254, 255, 237, 198, 170, 92, 26)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(92, 168, 59, 39, 78, 228, 188, 146)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__1);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_5_);
lean_ctor_set(v___x_6_, 2, v___x_5_);
lean_ctor_set(v___x_6_, 3, v___x_5_);
lean_ctor_set(v___x_6_, 4, v___x_4_);
lean_ctor_set(v___x_6_, 5, v___x_4_);
lean_ctor_set(v___x_6_, 6, v___x_4_);
lean_ctor_set(v___x_6_, 7, v___x_4_);
lean_ctor_set(v___x_6_, 8, v___x_4_);
lean_ctor_set(v___x_6_, 9, v___x_4_);
lean_ctor_set(v___x_6_, 10, v___x_4_);
return v___x_6_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_7_; double v___x_8_; 
v___x_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_float_of_nat(v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(lean_object* v_cls_12_, lean_object* v_msg_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_toCold_19_; lean_object* v_ref_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v_toCold_19_ = lean_ctor_get(v___y_16_, 0);
v_ref_20_ = lean_ctor_get(v___y_16_, 2);
v___x_21_ = lean_st_ref_get(v___y_17_);
v___x_22_ = lean_st_ref_get(v___y_15_);
v___x_23_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_14_);
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v_a_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_83_; 
v_a_24_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_83_ == 0)
{
v___x_26_ = v___x_23_;
v_isShared_27_ = v_isSharedCheck_83_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_a_24_);
lean_dec(v___x_23_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_83_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v_env_28_; lean_object* v_lctx_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_81_; 
v_env_28_ = lean_ctor_get(v___x_21_, 0);
lean_inc_ref(v_env_28_);
lean_dec(v___x_21_);
v_lctx_29_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_81_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_81_ == 0)
{
lean_object* v_unused_82_; 
v_unused_82_ = lean_ctor_get(v___x_22_, 1);
lean_dec(v_unused_82_);
v___x_31_ = v___x_22_;
v_isShared_32_ = v_isSharedCheck_81_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_lctx_29_);
lean_dec(v___x_22_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_81_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v_options_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v_traceState_36_; lean_object* v_env_37_; lean_object* v_nextMacroScope_38_; lean_object* v_ngen_39_; lean_object* v_auxDeclNGen_40_; lean_object* v_cache_41_; lean_object* v_messages_42_; lean_object* v_infoState_43_; lean_object* v_snapshotTasks_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_80_; 
v_options_33_ = lean_ctor_get(v_toCold_19_, 2);
v___x_34_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__2);
v___x_35_ = lean_st_ref_take(v___y_17_);
v_traceState_36_ = lean_ctor_get(v___x_35_, 4);
v_env_37_ = lean_ctor_get(v___x_35_, 0);
v_nextMacroScope_38_ = lean_ctor_get(v___x_35_, 1);
v_ngen_39_ = lean_ctor_get(v___x_35_, 2);
v_auxDeclNGen_40_ = lean_ctor_get(v___x_35_, 3);
v_cache_41_ = lean_ctor_get(v___x_35_, 5);
v_messages_42_ = lean_ctor_get(v___x_35_, 6);
v_infoState_43_ = lean_ctor_get(v___x_35_, 7);
v_snapshotTasks_44_ = lean_ctor_get(v___x_35_, 8);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_80_ == 0)
{
v___x_46_ = v___x_35_;
v_isShared_47_ = v_isSharedCheck_80_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_snapshotTasks_44_);
lean_inc(v_infoState_43_);
lean_inc(v_messages_42_);
lean_inc(v_cache_41_);
lean_inc(v_traceState_36_);
lean_inc(v_auxDeclNGen_40_);
lean_inc(v_ngen_39_);
lean_inc(v_nextMacroScope_38_);
lean_inc(v_env_37_);
lean_dec(v___x_35_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_80_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
uint64_t v_tid_48_; lean_object* v_traces_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_79_; 
v_tid_48_ = lean_ctor_get_uint64(v_traceState_36_, sizeof(void*)*1);
v_traces_49_ = lean_ctor_get(v_traceState_36_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v_traceState_36_);
if (v_isSharedCheck_79_ == 0)
{
v___x_51_ = v_traceState_36_;
v_isShared_52_ = v_isSharedCheck_79_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_traces_49_);
lean_dec(v_traceState_36_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_79_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
uint8_t v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_57_; 
v___x_53_ = lean_unbox(v_a_24_);
lean_dec(v_a_24_);
v___x_54_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_29_, v___x_53_);
lean_dec_ref(v_lctx_29_);
lean_inc_ref(v_options_33_);
v___x_55_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_55_, 0, v_env_28_);
lean_ctor_set(v___x_55_, 1, v___x_34_);
lean_ctor_set(v___x_55_, 2, v___x_54_);
lean_ctor_set(v___x_55_, 3, v_options_33_);
if (v_isShared_32_ == 0)
{
lean_ctor_set_tag(v___x_31_, 3);
lean_ctor_set(v___x_31_, 1, v_msg_13_);
lean_ctor_set(v___x_31_, 0, v___x_55_);
v___x_57_ = v___x_31_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_55_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v_msg_13_);
v___x_57_ = v_reuseFailAlloc_78_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
lean_object* v___x_58_; double v___x_59_; uint8_t v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_68_; 
v___x_58_ = lean_box(0);
v___x_59_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__3);
v___x_60_ = 0;
v___x_61_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__4));
v___x_62_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_62_, 0, v_cls_12_);
lean_ctor_set(v___x_62_, 1, v___x_58_);
lean_ctor_set(v___x_62_, 2, v___x_61_);
lean_ctor_set_float(v___x_62_, sizeof(void*)*3, v___x_59_);
lean_ctor_set_float(v___x_62_, sizeof(void*)*3 + 8, v___x_59_);
lean_ctor_set_uint8(v___x_62_, sizeof(void*)*3 + 16, v___x_60_);
v___x_63_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__5));
v___x_64_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_64_, 0, v___x_62_);
lean_ctor_set(v___x_64_, 1, v___x_57_);
lean_ctor_set(v___x_64_, 2, v___x_63_);
lean_inc(v_ref_20_);
v___x_65_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_65_, 0, v_ref_20_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
v___x_66_ = l_Lean_PersistentArray_push___redArg(v_traces_49_, v___x_65_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 0, v___x_66_);
v___x_68_ = v___x_51_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v___x_66_);
lean_ctor_set_uint64(v_reuseFailAlloc_77_, sizeof(void*)*1, v_tid_48_);
v___x_68_ = v_reuseFailAlloc_77_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
lean_object* v___x_70_; 
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 4, v___x_68_);
v___x_70_ = v___x_46_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_env_37_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v_nextMacroScope_38_);
lean_ctor_set(v_reuseFailAlloc_76_, 2, v_ngen_39_);
lean_ctor_set(v_reuseFailAlloc_76_, 3, v_auxDeclNGen_40_);
lean_ctor_set(v_reuseFailAlloc_76_, 4, v___x_68_);
lean_ctor_set(v_reuseFailAlloc_76_, 5, v_cache_41_);
lean_ctor_set(v_reuseFailAlloc_76_, 6, v_messages_42_);
lean_ctor_set(v_reuseFailAlloc_76_, 7, v_infoState_43_);
lean_ctor_set(v_reuseFailAlloc_76_, 8, v_snapshotTasks_44_);
v___x_70_ = v_reuseFailAlloc_76_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_74_; 
v___x_71_ = lean_st_ref_put(v___y_17_, v___x_70_);
v___x_72_ = lean_box(0);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 0, v___x_72_);
v___x_74_ = v___x_26_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v___x_72_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
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
lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_91_; 
lean_dec(v___x_22_);
lean_dec(v___x_21_);
lean_dec_ref(v_msg_13_);
lean_dec(v_cls_12_);
v_a_84_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_91_ == 0)
{
v___x_86_ = v___x_23_;
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_dec(v___x_23_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_89_; 
if (v_isShared_87_ == 0)
{
v___x_89_ = v___x_86_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_a_84_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___boxed(lean_object* v_cls_92_, lean_object* v_msg_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v_cls_92_, v_msg_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0(lean_object* v_cls_100_, lean_object* v_msg_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v_cls_100_, v_msg_101_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___boxed(lean_object* v_cls_111_, lean_object* v_msg_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0(v_cls_111_, v_msg_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec_ref(v___y_115_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
return v_res_121_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3));
v___x_133_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5));
v___x_134_ = l_Lean_Name_append(v___x_133_, v___x_132_);
return v___x_134_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7));
v___x_137_ = l_Lean_stringToMessageData(v___x_136_);
return v___x_137_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9));
v___x_140_ = l_Lean_stringToMessageData(v___x_139_);
return v___x_140_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11));
v___x_143_ = l_Lean_stringToMessageData(v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13));
v___x_146_ = l_Lean_stringToMessageData(v___x_145_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16));
v___x_150_ = l_Lean_stringToMessageData(v___x_149_);
return v___x_150_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19));
v___x_157_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5));
v___x_158_ = l_Lean_Name_append(v___x_157_, v___x_156_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23));
v___x_167_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5));
v___x_168_ = l_Lean_Name_append(v___x_167_, v___x_166_);
return v___x_168_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__25));
v___x_171_ = l_Lean_stringToMessageData(v___x_170_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__27(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = lean_unsigned_to_nat(2u);
v___x_173_ = lean_nat_to_int(v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f(lean_object* v_decl_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v_toSignature_183_; lean_object* v_value_184_; uint8_t v_recursive_185_; lean_object* v_inlineAttr_x3f_186_; lean_object* v___y_188_; lean_object* v___y_189_; lean_object* v___y_190_; lean_object* v___y_191_; lean_object* v___y_192_; lean_object* v___y_193_; 
v_toSignature_183_ = lean_ctor_get(v_decl_174_, 0);
lean_inc_ref(v_toSignature_183_);
v_value_184_ = lean_ctor_get(v_decl_174_, 1);
lean_inc_ref(v_value_184_);
v_recursive_185_ = lean_ctor_get_uint8(v_decl_174_, sizeof(void*)*3);
v_inlineAttr_x3f_186_ = lean_ctor_get(v_decl_174_, 2);
lean_inc(v_inlineAttr_x3f_186_);
if (lean_obj_tag(v_value_184_) == 0)
{
lean_object* v_code_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_431_; 
v_code_247_ = lean_ctor_get(v_value_184_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v_value_184_);
if (v_isSharedCheck_431_ == 0)
{
v___x_249_ = v_value_184_;
v_isShared_250_ = v_isSharedCheck_431_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_code_247_);
lean_dec(v_value_184_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_431_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
uint8_t v___x_251_; lean_object* v___x_252_; 
v___x_251_ = 0;
lean_inc_ref(v_code_247_);
v___x_252_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(v_code_247_, v___x_251_, v_a_176_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_toCold_253_; lean_object* v_options_254_; lean_object* v_inheritedTraceOptions_255_; uint8_t v_hasTrace_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___y_260_; uint8_t v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; uint8_t v___y_307_; lean_object* v___y_308_; 
lean_dec_ref_known(v___x_252_, 1);
v_toCold_253_ = lean_ctor_get(v_a_180_, 0);
v_options_254_ = lean_ctor_get(v_toCold_253_, 2);
v_inheritedTraceOptions_255_ = lean_ctor_get(v_toCold_253_, 11);
v_hasTrace_256_ = lean_ctor_get_uint8(v_options_254_, sizeof(void*)*1);
v___x_257_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0));
v___x_258_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1));
if (v_hasTrace_256_ == 0)
{
goto v___jp_365_;
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_391_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23));
v___x_392_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24);
v___x_393_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_255_, v_options_254_, v___x_392_);
if (v___x_393_ == 0)
{
goto v___jp_365_;
}
else
{
lean_object* v___x_394_; lean_object* v_funDeclInfoMap_395_; lean_object* v___x_396_; 
v___x_394_ = lean_st_ref_get(v_a_176_);
v_funDeclInfoMap_395_ = lean_ctor_get(v___x_394_, 3);
lean_inc_ref(v_funDeclInfoMap_395_);
lean_dec(v___x_394_);
v___x_396_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(v_funDeclInfoMap_395_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
lean_dec_ref(v_funDeclInfoMap_395_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v_name_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc(v_a_397_);
lean_dec_ref_known(v___x_396_, 1);
v_name_398_ = lean_ctor_get(v_toSignature_183_, 0);
lean_inc(v_name_398_);
v___x_399_ = l_Lean_MessageData_ofName(v_name_398_);
v___x_400_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26);
v___x_401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_399_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__27, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__27_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__27);
v___x_403_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v_a_397_);
v___x_404_ = l_Lean_MessageData_ofFormat(v___x_403_);
v___x_405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_401_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v___x_391_, v___x_405_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_dec_ref_known(v___x_406_, 1);
goto v___jp_365_;
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_del_object(v___x_249_);
lean_dec_ref(v_code_247_);
lean_dec(v_inlineAttr_x3f_186_);
lean_dec_ref(v_toSignature_183_);
lean_dec_ref(v_decl_174_);
v_a_407_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_406_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_406_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
lean_del_object(v___x_249_);
lean_dec_ref(v_code_247_);
lean_dec(v_inlineAttr_x3f_186_);
lean_dec_ref(v_toSignature_183_);
lean_dec_ref(v_decl_174_);
v_a_415_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_396_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_396_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
v___jp_259_:
{
if (v_hasTrace_256_ == 0)
{
lean_dec(v___y_263_);
lean_dec(v___y_262_);
lean_dec(v___y_260_);
lean_del_object(v___x_249_);
v___y_188_ = v___y_264_;
v___y_189_ = v_a_176_;
v___y_190_ = v_a_178_;
v___y_191_ = v_a_179_;
v___y_192_ = v_a_180_;
v___y_193_ = v_a_181_;
goto v___jp_187_;
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_265_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3));
v___x_266_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6);
v___x_267_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_255_, v_options_254_, v___x_266_);
if (v___x_267_ == 0)
{
lean_dec(v___y_263_);
lean_dec(v___y_262_);
lean_dec(v___y_260_);
lean_del_object(v___x_249_);
v___y_188_ = v___y_264_;
v___y_189_ = v_a_176_;
v___y_190_ = v_a_178_;
v___y_191_ = v_a_179_;
v___y_192_ = v_a_180_;
v___y_193_ = v_a_181_;
goto v___jp_187_;
}
else
{
lean_object* v_name_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v_name_268_ = lean_ctor_get(v_toSignature_183_, 0);
lean_inc(v_name_268_);
v___x_269_ = l_Lean_MessageData_ofName(v_name_268_);
v___x_270_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8);
v___x_271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_269_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = l_Lean_Compiler_LCNF_Code_size(v___y_261_, v___y_264_);
v___x_273_ = l_Nat_reprFast(v___x_272_);
if (v_isShared_250_ == 0)
{
lean_ctor_set_tag(v___x_249_, 3);
lean_ctor_set(v___x_249_, 0, v___x_273_);
v___x_275_ = v___x_249_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_305_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_276_ = l_Lean_MessageData_ofFormat(v___x_275_);
v___x_277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_271_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v___x_278_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10);
v___x_279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_277_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v___x_280_ = l_Nat_reprFast(v___y_262_);
v___x_281_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
v___x_282_ = l_Lean_MessageData_ofFormat(v___x_281_);
v___x_283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_279_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___x_284_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12);
v___x_285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_283_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = l_Nat_reprFast(v___y_260_);
v___x_287_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
v___x_288_ = l_Lean_MessageData_ofFormat(v___x_287_);
v___x_289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_285_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14);
v___x_291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_289_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = l_Nat_reprFast(v___y_263_);
v___x_293_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
v___x_294_ = l_Lean_MessageData_ofFormat(v___x_293_);
v___x_295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_291_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v___x_265_, v___x_295_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_dec_ref_known(v___x_296_, 1);
v___y_188_ = v___y_264_;
v___y_189_ = v_a_176_;
v___y_190_ = v_a_178_;
v___y_191_ = v_a_179_;
v___y_192_ = v_a_180_;
v___y_193_ = v_a_181_;
goto v___jp_187_;
}
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
lean_dec_ref(v___y_264_);
lean_dec(v_inlineAttr_x3f_186_);
lean_dec_ref(v_toSignature_183_);
v_a_297_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_296_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
}
}
}
v___jp_306_:
{
lean_object* v___x_309_; 
lean_inc_ref(v_a_180_);
v___x_309_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_247_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; lean_object* v___x_311_; lean_object* v_binderRenaming_312_; lean_object* v_visited_313_; lean_object* v_inline_314_; lean_object* v_inlineLocal_315_; lean_object* v___x_316_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_a_310_);
lean_dec_ref_known(v___x_309_, 1);
v___x_311_ = lean_st_ref_get(v_a_176_);
v_binderRenaming_312_ = lean_ctor_get(v___x_311_, 2);
lean_inc(v_binderRenaming_312_);
v_visited_313_ = lean_ctor_get(v___x_311_, 4);
lean_inc(v_visited_313_);
v_inline_314_ = lean_ctor_get(v___x_311_, 5);
lean_inc(v_inline_314_);
v_inlineLocal_315_ = lean_ctor_get(v___x_311_, 6);
lean_inc(v_inlineLocal_315_);
lean_dec(v___x_311_);
v___x_316_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v___y_307_, v_a_310_, v_binderRenaming_312_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
lean_dec(v_binderRenaming_312_);
if (lean_obj_tag(v___x_316_) == 0)
{
if (v_hasTrace_256_ == 0)
{
lean_object* v_a_317_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_a_317_);
lean_dec_ref_known(v___x_316_, 1);
v___y_260_ = v_inline_314_;
v___y_261_ = v___y_307_;
v___y_262_ = v_visited_313_;
v___y_263_ = v_inlineLocal_315_;
v___y_264_ = v_a_317_;
goto v___jp_259_;
}
else
{
lean_object* v_a_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v_a_318_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_a_318_);
lean_dec_ref_known(v___x_316_, 1);
v___x_319_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15));
lean_inc_ref(v___y_308_);
v___x_320_ = l_Lean_Name_mkStr4(v___x_257_, v___x_258_, v___y_308_, v___x_319_);
v___x_321_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5));
lean_inc(v___x_320_);
v___x_322_ = l_Lean_Name_append(v___x_321_, v___x_320_);
v___x_323_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_255_, v_options_254_, v___x_322_);
lean_dec(v___x_322_);
if (v___x_323_ == 0)
{
lean_dec(v___x_320_);
v___y_260_ = v_inline_314_;
v___y_261_ = v___y_307_;
v___y_262_ = v_visited_313_;
v___y_263_ = v_inlineLocal_315_;
v___y_264_ = v_a_318_;
goto v___jp_259_;
}
else
{
lean_object* v___x_324_; 
lean_inc(v_a_318_);
v___x_324_ = l_Lean_Compiler_LCNF_ppCode(v___y_307_, v_a_318_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v_name_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_325_);
lean_dec_ref_known(v___x_324_, 1);
v_name_326_ = lean_ctor_get(v_toSignature_183_, 0);
lean_inc(v_name_326_);
v___x_327_ = l_Lean_MessageData_ofName(v_name_326_);
v___x_328_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17);
v___x_329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_327_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = l_Lean_MessageData_ofFormat(v_a_325_);
v___x_331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_329_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v___x_320_, v___x_331_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_dec_ref_known(v___x_332_, 1);
v___y_260_ = v_inline_314_;
v___y_261_ = v___y_307_;
v___y_262_ = v_visited_313_;
v___y_263_ = v_inlineLocal_315_;
v___y_264_ = v_a_318_;
goto v___jp_259_;
}
else
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
lean_dec(v_a_318_);
lean_dec(v_inlineLocal_315_);
lean_dec(v_inline_314_);
lean_dec(v_visited_313_);
lean_del_object(v___x_249_);
lean_dec(v_inlineAttr_x3f_186_);
lean_dec_ref(v_toSignature_183_);
v_a_333_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_332_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_332_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_333_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
lean_dec(v___x_320_);
lean_dec(v_a_318_);
lean_dec(v_inlineLocal_315_);
lean_dec(v_inline_314_);
lean_dec(v_visited_313_);
lean_del_object(v___x_249_);
lean_dec(v_inlineAttr_x3f_186_);
lean_dec_ref(v_toSignature_183_);
v_a_341_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_324_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_324_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
lean_dec(v_inlineLocal_315_);
lean_dec(v_inline_314_);
lean_dec(v_visited_313_);
lean_del_object(v___x_249_);
lean_dec(v_inlineAttr_x3f_186_);
lean_dec_ref(v_toSignature_183_);
v_a_349_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_316_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_316_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
else
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
lean_del_object(v___x_249_);
lean_dec(v_inlineAttr_x3f_186_);
lean_dec_ref(v_toSignature_183_);
v_a_357_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v___x_309_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_309_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_357_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
v___jp_365_:
{
lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_366_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18));
v___x_367_ = 0;
if (v_hasTrace_256_ == 0)
{
lean_dec_ref(v_decl_174_);
v___y_307_ = v___x_367_;
v___y_308_ = v___x_366_;
goto v___jp_306_;
}
else
{
lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_368_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19));
v___x_369_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20);
v___x_370_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_255_, v_options_254_, v___x_369_);
if (v___x_370_ == 0)
{
lean_dec_ref(v_decl_174_);
v___y_307_ = v___x_367_;
v___y_308_ = v___x_366_;
goto v___jp_306_;
}
else
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_Compiler_LCNF_ppDecl(v___x_367_, v_decl_174_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_372_);
lean_dec_ref_known(v___x_371_, 1);
v___x_373_ = l_Lean_MessageData_ofFormat(v_a_372_);
v___x_374_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v___x_368_, v___x_373_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_dec_ref_known(v___x_374_, 1);
v___y_307_ = v___x_367_;
v___y_308_ = v___x_366_;
goto v___jp_306_;
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_del_object(v___x_249_);
lean_dec_ref(v_code_247_);
lean_dec(v_inlineAttr_x3f_186_);
lean_dec_ref(v_toSignature_183_);
v_a_375_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_374_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_374_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_del_object(v___x_249_);
lean_dec_ref(v_code_247_);
lean_dec(v_inlineAttr_x3f_186_);
lean_dec_ref(v_toSignature_183_);
v_a_383_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_371_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_371_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
lean_del_object(v___x_249_);
lean_dec_ref(v_code_247_);
lean_dec(v_inlineAttr_x3f_186_);
lean_dec_ref(v_toSignature_183_);
lean_dec_ref(v_decl_174_);
v_a_423_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_252_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_252_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
else
{
lean_object* v___x_432_; lean_object* v___x_433_; 
lean_dec(v_inlineAttr_x3f_186_);
lean_dec_ref(v_value_184_);
lean_dec_ref(v_toSignature_183_);
lean_dec_ref(v_decl_174_);
v___x_432_ = lean_box(0);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
v___jp_187_:
{
lean_object* v___x_194_; 
lean_inc_ref(v___y_188_);
v___x_194_ = l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(v___y_188_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_238_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_238_ == 0)
{
v___x_197_ = v___x_194_;
v_isShared_198_ = v_isSharedCheck_238_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_194_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_238_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
if (lean_obj_tag(v_a_195_) == 1)
{
lean_object* v_val_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_225_; 
lean_del_object(v___x_197_);
lean_dec_ref(v___y_188_);
v_val_199_ = lean_ctor_get(v_a_195_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v_a_195_);
if (v_isSharedCheck_225_ == 0)
{
v___x_201_ = v_a_195_;
v_isShared_202_ = v_isSharedCheck_225_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_val_199_);
lean_dec(v_a_195_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_225_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v_val_199_);
v___x_204_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_204_, 0, v_toSignature_183_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
lean_ctor_set(v___x_204_, 2, v_inlineAttr_x3f_186_);
lean_ctor_set_uint8(v___x_204_, sizeof(void*)*3, v_recursive_185_);
v___x_205_ = l_Lean_Compiler_LCNF_Decl_reduceJpArity(v___x_204_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_216_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_216_ == 0)
{
v___x_208_ = v___x_205_;
v_isShared_209_ = v_isSharedCheck_216_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_205_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_216_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v_a_206_);
v___x_211_ = v___x_201_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_a_206_);
v___x_211_ = v_reuseFailAlloc_215_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_213_; 
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_211_);
v___x_213_ = v___x_208_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
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
else
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_224_; 
lean_del_object(v___x_201_);
v_a_217_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_224_ == 0)
{
v___x_219_ = v___x_205_;
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_205_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_222_; 
if (v_isShared_220_ == 0)
{
v___x_222_ = v___x_219_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_a_217_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
}
else
{
lean_object* v___x_226_; uint8_t v_simplified_227_; 
lean_dec(v_a_195_);
v___x_226_ = lean_st_ref_get(v___y_189_);
v_simplified_227_ = lean_ctor_get_uint8(v___x_226_, sizeof(void*)*7);
lean_dec(v___x_226_);
if (v_simplified_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_230_; 
lean_dec_ref(v___y_188_);
lean_dec(v_inlineAttr_x3f_186_);
lean_dec_ref(v_toSignature_183_);
v___x_228_ = lean_box(0);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___x_228_);
v___x_230_ = v___x_197_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v___y_188_);
v___x_233_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_233_, 0, v_toSignature_183_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
lean_ctor_set(v___x_233_, 2, v_inlineAttr_x3f_186_);
lean_ctor_set_uint8(v___x_233_, sizeof(void*)*3, v_recursive_185_);
v___x_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___x_234_);
v___x_236_ = v___x_197_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
else
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
lean_dec_ref(v___y_188_);
lean_dec(v_inlineAttr_x3f_186_);
lean_dec_ref(v_toSignature_183_);
v_a_239_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___x_194_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_194_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___boxed(lean_object* v_decl_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Compiler_LCNF_Decl_simp_x3f(v_decl_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
return v_res_443_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = lean_box(0);
v___x_445_ = lean_unsigned_to_nat(16u);
v___x_446_ = lean_mk_array(v___x_445_, v___x_444_);
return v___x_446_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0, &l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0);
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set(v___x_449_, 1, v___x_447_);
return v___x_449_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2(void){
_start:
{
lean_object* v___x_450_; uint8_t v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = 0;
v___x_452_ = lean_box(1);
v___x_453_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1, &l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1);
v___x_454_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_454_, 0, v___x_453_);
lean_ctor_set(v___x_454_, 1, v___x_452_);
lean_ctor_set(v___x_454_, 2, v___x_452_);
lean_ctor_set(v___x_454_, 3, v___x_453_);
lean_ctor_set(v___x_454_, 4, v___x_450_);
lean_ctor_set(v___x_454_, 5, v___x_450_);
lean_ctor_set(v___x_454_, 6, v___x_450_);
lean_ctor_set_uint8(v___x_454_, sizeof(void*)*7, v___x_451_);
return v___x_454_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3(void){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_455_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3, &l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__5(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4, &l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4_once, _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4);
v___x_459_ = lean_box(1);
v___x_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
lean_ctor_set(v___x_460_, 1, v___x_458_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go(lean_object* v_decl_461_, lean_object* v_config_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v_toSignature_470_; lean_object* v_name_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_468_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2, &l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2_once, _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2);
v___x_469_ = lean_st_mk_ref(v___x_468_);
v_toSignature_470_ = lean_ctor_get(v_decl_461_, 0);
v_name_471_ = lean_ctor_get(v_toSignature_470_, 0);
v___x_472_ = lean_box(0);
v___x_473_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4, &l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4_once, _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4);
lean_inc_ref(v_config_462_);
lean_inc(v_name_471_);
v___x_474_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_474_, 0, v_name_471_);
lean_ctor_set(v___x_474_, 1, v_config_462_);
lean_ctor_set(v___x_474_, 2, v___x_472_);
lean_ctor_set(v___x_474_, 3, v___x_473_);
v___x_475_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__5, &l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__5_once, _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__5);
lean_inc_ref(v_decl_461_);
v___x_476_ = l_Lean_Compiler_LCNF_Decl_simp_x3f(v_decl_461_, v___x_474_, v___x_469_, v___x_475_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
lean_dec_ref_known(v___x_474_, 4);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_487_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_487_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_487_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_487_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; 
v___x_481_ = lean_st_ref_get(v___x_469_);
lean_dec(v___x_469_);
lean_dec(v___x_481_);
if (lean_obj_tag(v_a_477_) == 1)
{
lean_object* v_val_482_; 
lean_del_object(v___x_479_);
lean_dec_ref(v_decl_461_);
v_val_482_ = lean_ctor_get(v_a_477_, 0);
lean_inc(v_val_482_);
lean_dec_ref_known(v_a_477_, 1);
v_decl_461_ = v_val_482_;
goto _start;
}
else
{
lean_object* v___x_485_; 
lean_dec(v_a_477_);
lean_dec_ref(v_config_462_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v_decl_461_);
v___x_485_ = v___x_479_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_decl_461_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec(v___x_469_);
lean_dec_ref(v_config_462_);
lean_dec_ref(v_decl_461_);
v_a_488_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_476_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_476_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___boxed(lean_object* v_decl_496_, lean_object* v_config_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go(v_decl_496_, v_config_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
lean_dec(v_a_501_);
lean_dec_ref(v_a_500_);
lean_dec(v_a_499_);
lean_dec_ref(v_a_498_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp(lean_object* v_decl_504_, lean_object* v_config_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
lean_object* v___x_511_; 
lean_inc_ref(v_decl_504_);
v___x_511_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(v_decl_504_, v_a_508_, v_a_509_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; uint8_t v___x_513_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref_known(v___x_511_, 1);
v___x_513_ = lean_unbox(v_a_512_);
lean_dec(v_a_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
v___x_514_ = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go(v_decl_504_, v_config_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_);
return v___x_514_;
}
else
{
uint8_t v_implementedBy_515_; uint8_t v_inlineDefs_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_525_; 
v_implementedBy_515_ = lean_ctor_get_uint8(v_config_505_, 2);
v_inlineDefs_516_ = lean_ctor_get_uint8(v_config_505_, 3);
v_isSharedCheck_525_ = !lean_is_exclusive(v_config_505_);
if (v_isSharedCheck_525_ == 0)
{
v___x_518_ = v_config_505_;
v_isShared_519_ = v_isSharedCheck_525_;
goto v_resetjp_517_;
}
else
{
lean_dec(v_config_505_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_525_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
uint8_t v___x_520_; lean_object* v___x_522_; 
v___x_520_ = 0;
if (v_isShared_519_ == 0)
{
v___x_522_ = v___x_518_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v_reuseFailAlloc_524_, 2, v_implementedBy_515_);
lean_ctor_set_uint8(v_reuseFailAlloc_524_, 3, v_inlineDefs_516_);
v___x_522_ = v_reuseFailAlloc_524_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; 
lean_ctor_set_uint8(v___x_522_, 0, v___x_520_);
lean_ctor_set_uint8(v___x_522_, 1, v___x_520_);
v___x_523_ = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go(v_decl_504_, v___x_522_, v_a_506_, v_a_507_, v_a_508_, v_a_509_);
return v___x_523_;
}
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec_ref(v_config_505_);
lean_dec_ref(v_decl_504_);
v_a_526_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_511_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_511_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp___boxed(lean_object* v_decl_534_, lean_object* v_config_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_Compiler_LCNF_Decl_simp(v_decl_534_, v_config_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___lam__0(lean_object* v_config_542_, lean_object* v_x_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_Compiler_LCNF_Decl_simp(v_x_543_, v_config_542_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___lam__0___boxed(lean_object* v_config_550_, lean_object* v_x_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_Compiler_LCNF_simp___lam__0(v_config_550_, v_x_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___lam__1(uint8_t v_phase_560_, lean_object* v___f_561_, lean_object* v_occurrence_562_, lean_object* v_h_563_){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = ((lean_object*)(l_Lean_Compiler_LCNF_simp___lam__1___closed__0));
v___x_565_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_564_, v_phase_560_, v___f_561_, v_occurrence_562_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___lam__1___boxed(lean_object* v_phase_566_, lean_object* v___f_567_, lean_object* v_occurrence_568_, lean_object* v_h_569_){
_start:
{
uint8_t v_phase_boxed_570_; lean_object* v_res_571_; 
v_phase_boxed_570_ = lean_unbox(v_phase_566_);
v_res_571_ = l_Lean_Compiler_LCNF_simp___lam__1(v_phase_boxed_570_, v___f_567_, v_occurrence_568_, v_h_569_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp(lean_object* v_config_572_, lean_object* v_occurrence_573_, uint8_t v_phase_574_){
_start:
{
lean_object* v___f_575_; lean_object* v___x_576_; lean_object* v___f_577_; lean_object* v___x_578_; uint8_t v___x_579_; lean_object* v___x_580_; 
v___f_575_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_simp___lam__0___boxed), 7, 1);
lean_closure_set(v___f_575_, 0, v_config_572_);
v___x_576_ = lean_box(v_phase_574_);
v___f_577_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_simp___lam__1___boxed), 4, 3);
lean_closure_set(v___f_577_, 0, v___x_576_);
lean_closure_set(v___f_577_, 1, v___f_575_);
lean_closure_set(v___f_577_, 2, v_occurrence_573_);
v___x_578_ = l_Lean_Compiler_LCNF_instInhabitedPass;
v___x_579_ = 0;
v___x_580_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___x_578_, v_phase_574_, v___x_579_, v___f_577_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___boxed(lean_object* v_config_581_, lean_object* v_occurrence_582_, lean_object* v_phase_583_){
_start:
{
uint8_t v_phase_boxed_584_; lean_object* v_res_585_; 
v_phase_boxed_584_ = lean_unbox(v_phase_583_);
v_res_585_ = l_Lean_Compiler_LCNF_simp(v_config_581_, v_occurrence_582_, v_phase_boxed_584_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_660_; uint8_t v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_660_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_));
v___x_661_ = 1;
v___x_662_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_));
v___x_663_ = l_Lean_registerTraceClass(v___x_660_, v___x_661_, v___x_662_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v___x_664_; uint8_t v___x_665_; lean_object* v___x_666_; 
lean_dec_ref_known(v___x_663_, 1);
v___x_664_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3));
v___x_665_ = 0;
v___x_666_ = l_Lean_registerTraceClass(v___x_664_, v___x_665_, v___x_662_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; 
lean_dec_ref_known(v___x_666_, 1);
v___x_667_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19));
v___x_668_ = l_Lean_registerTraceClass(v___x_667_, v___x_665_, v___x_662_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v___x_669_; lean_object* v___x_670_; 
lean_dec_ref_known(v___x_668_, 1);
v___x_669_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_));
v___x_670_ = l_Lean_registerTraceClass(v___x_669_, v___x_665_, v___x_662_);
return v___x_670_;
}
else
{
return v___x_668_;
}
}
else
{
return v___x_666_;
}
}
else
{
return v___x_663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2____boxed(lean_object* v_a_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
return v_res_672_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

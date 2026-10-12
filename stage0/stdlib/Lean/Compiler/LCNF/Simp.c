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
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_take(lean_object*);
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
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_4_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_5_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__1);
v___x_6_ = lean_unsigned_to_nat(0u);
v___x_7_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
lean_ctor_set(v___x_7_, 1, v___x_6_);
lean_ctor_set(v___x_7_, 2, v___x_6_);
lean_ctor_set(v___x_7_, 3, v___x_6_);
lean_ctor_set(v___x_7_, 4, v___x_5_);
lean_ctor_set(v___x_7_, 5, v___x_5_);
lean_ctor_set(v___x_7_, 6, v___x_5_);
lean_ctor_set(v___x_7_, 7, v___x_5_);
lean_ctor_set(v___x_7_, 8, v___x_5_);
lean_ctor_set(v___x_7_, 9, v___x_5_);
lean_ctor_set(v___x_7_, 10, v___x_5_);
lean_ctor_set(v___x_7_, 11, v___x_4_);
return v___x_7_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_8_; double v___x_9_; 
v___x_8_ = lean_unsigned_to_nat(0u);
v___x_9_ = lean_float_of_nat(v___x_8_);
return v___x_9_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(lean_object* v_cls_13_, lean_object* v_msg_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v_ref_20_; lean_object* v___x_21_; lean_object* v_env_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v_ref_20_ = lean_ctor_get(v___y_17_, 2);
v___x_21_ = lean_st_ref_get(v___y_18_);
v_env_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc_ref(v_env_22_);
lean_dec(v___x_21_);
v___x_23_ = lean_st_ref_get(v___y_16_);
v___x_24_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_15_);
if (lean_obj_tag(v___x_24_) == 0)
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_84_; 
v_a_25_ = lean_ctor_get(v___x_24_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_24_);
if (v_isSharedCheck_84_ == 0)
{
v___x_27_ = v___x_24_;
v_isShared_28_ = v_isSharedCheck_84_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_24_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_84_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v_lctx_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_82_; 
v_lctx_29_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_82_ == 0)
{
lean_object* v_unused_83_; 
v_unused_83_ = lean_ctor_get(v___x_23_, 1);
lean_dec(v_unused_83_);
v___x_31_ = v___x_23_;
v_isShared_32_ = v_isSharedCheck_82_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_lctx_29_);
lean_dec(v___x_23_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_82_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
uint8_t v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_39_; 
v___x_33_ = lean_unbox(v_a_25_);
lean_dec(v_a_25_);
v___x_34_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_29_, v___x_33_);
lean_dec_ref(v_lctx_29_);
v___x_35_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_17_);
v___x_36_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__2);
v___x_37_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_37_, 0, v_env_22_);
lean_ctor_set(v___x_37_, 1, v___x_36_);
lean_ctor_set(v___x_37_, 2, v___x_34_);
lean_ctor_set(v___x_37_, 3, v___x_35_);
if (v_isShared_32_ == 0)
{
lean_ctor_set_tag(v___x_31_, 3);
lean_ctor_set(v___x_31_, 1, v_msg_14_);
lean_ctor_set(v___x_31_, 0, v___x_37_);
v___x_39_ = v___x_31_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_37_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_msg_14_);
v___x_39_ = v_reuseFailAlloc_81_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
lean_object* v___x_40_; lean_object* v_traceState_41_; lean_object* v_env_42_; lean_object* v_nextMacroScope_43_; lean_object* v_ngen_44_; lean_object* v_auxDeclNGen_45_; lean_object* v_cache_46_; lean_object* v_recordedDeps_47_; lean_object* v_messages_48_; lean_object* v_infoState_49_; lean_object* v_snapshotTasks_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_80_; 
v___x_40_ = lean_st_ref_take(v___y_18_);
v_traceState_41_ = lean_ctor_get(v___x_40_, 4);
v_env_42_ = lean_ctor_get(v___x_40_, 0);
v_nextMacroScope_43_ = lean_ctor_get(v___x_40_, 1);
v_ngen_44_ = lean_ctor_get(v___x_40_, 2);
v_auxDeclNGen_45_ = lean_ctor_get(v___x_40_, 3);
v_cache_46_ = lean_ctor_get(v___x_40_, 5);
v_recordedDeps_47_ = lean_ctor_get(v___x_40_, 6);
v_messages_48_ = lean_ctor_get(v___x_40_, 7);
v_infoState_49_ = lean_ctor_get(v___x_40_, 8);
v_snapshotTasks_50_ = lean_ctor_get(v___x_40_, 9);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_80_ == 0)
{
v___x_52_ = v___x_40_;
v_isShared_53_ = v_isSharedCheck_80_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_snapshotTasks_50_);
lean_inc(v_infoState_49_);
lean_inc(v_messages_48_);
lean_inc(v_recordedDeps_47_);
lean_inc(v_cache_46_);
lean_inc(v_traceState_41_);
lean_inc(v_auxDeclNGen_45_);
lean_inc(v_ngen_44_);
lean_inc(v_nextMacroScope_43_);
lean_inc(v_env_42_);
lean_dec(v___x_40_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_80_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
uint64_t v_tid_54_; lean_object* v_traces_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_79_; 
v_tid_54_ = lean_ctor_get_uint64(v_traceState_41_, sizeof(void*)*1);
v_traces_55_ = lean_ctor_get(v_traceState_41_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v_traceState_41_);
if (v_isSharedCheck_79_ == 0)
{
v___x_57_ = v_traceState_41_;
v_isShared_58_ = v_isSharedCheck_79_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_traces_55_);
lean_dec(v_traceState_41_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_79_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_59_; lean_object* v___x_60_; double v___x_61_; uint8_t v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_70_; 
v___x_59_ = lean_box(0);
v___x_60_ = lean_box(0);
v___x_61_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__3);
v___x_62_ = 0;
v___x_63_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__4));
v___x_64_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_64_, 0, v_cls_13_);
lean_ctor_set(v___x_64_, 1, v___x_60_);
lean_ctor_set(v___x_64_, 2, v___x_63_);
lean_ctor_set_float(v___x_64_, sizeof(void*)*3, v___x_61_);
lean_ctor_set_float(v___x_64_, sizeof(void*)*3 + 8, v___x_61_);
lean_ctor_set_uint8(v___x_64_, sizeof(void*)*3 + 16, v___x_62_);
v___x_65_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__5));
v___x_66_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_66_, 0, v___x_64_);
lean_ctor_set(v___x_66_, 1, v___x_39_);
lean_ctor_set(v___x_66_, 2, v___x_65_);
lean_inc(v_ref_20_);
v___x_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_67_, 0, v_ref_20_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = l_Lean_PersistentArray_push___redArg(v_traces_55_, v___x_67_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_68_);
v___x_70_ = v___x_57_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_68_);
lean_ctor_set_uint64(v_reuseFailAlloc_78_, sizeof(void*)*1, v_tid_54_);
v___x_70_ = v_reuseFailAlloc_78_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
lean_object* v___x_72_; 
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 4, v___x_70_);
v___x_72_ = v___x_52_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_env_42_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v_nextMacroScope_43_);
lean_ctor_set(v_reuseFailAlloc_77_, 2, v_ngen_44_);
lean_ctor_set(v_reuseFailAlloc_77_, 3, v_auxDeclNGen_45_);
lean_ctor_set(v_reuseFailAlloc_77_, 4, v___x_70_);
lean_ctor_set(v_reuseFailAlloc_77_, 5, v_cache_46_);
lean_ctor_set(v_reuseFailAlloc_77_, 6, v_recordedDeps_47_);
lean_ctor_set(v_reuseFailAlloc_77_, 7, v_messages_48_);
lean_ctor_set(v_reuseFailAlloc_77_, 8, v_infoState_49_);
lean_ctor_set(v_reuseFailAlloc_77_, 9, v_snapshotTasks_50_);
v___x_72_ = v_reuseFailAlloc_77_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_73_; lean_object* v___x_75_; 
v___x_73_ = lean_st_ref_put(v___y_18_, v___x_72_);
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 0, v___x_59_);
v___x_75_ = v___x_27_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v___x_59_);
v___x_75_ = v_reuseFailAlloc_76_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
return v___x_75_;
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
lean_object* v_a_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_92_; 
lean_dec(v___x_23_);
lean_dec_ref(v_env_22_);
lean_dec_ref(v_msg_14_);
lean_dec(v_cls_13_);
v_a_85_ = lean_ctor_get(v___x_24_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v___x_24_);
if (v_isSharedCheck_92_ == 0)
{
v___x_87_ = v___x_24_;
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_a_85_);
lean_dec(v___x_24_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_90_; 
if (v_isShared_88_ == 0)
{
v___x_90_ = v___x_87_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_a_85_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_13_ = stack[0].m_obj;
lean_object* v_msg_14_ = stack[1].m_obj;
lean_object* v___y_15_ = stack[2].m_obj;
lean_object* v___y_16_ = stack[3].m_obj;
lean_object* v___y_17_ = stack[4].m_obj;
lean_object* v___y_18_ = stack[5].m_obj;
lean_object* v_res_93_;
v_res_93_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v_cls_13_, v_msg_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
stack->m_obj
 = v_res_93_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___boxed(lean_object* v_cls_94_, lean_object* v_msg_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v_cls_94_, v_msg_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
return v_res_101_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0(lean_object* v_cls_102_, lean_object* v_msg_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v_cls_102_, v_msg_103_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
return v___x_112_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_102_ = stack[0].m_obj;
lean_object* v_msg_103_ = stack[1].m_obj;
lean_object* v___y_104_ = stack[2].m_obj;
lean_object* v___y_105_ = stack[3].m_obj;
lean_object* v___y_106_ = stack[4].m_obj;
lean_object* v___y_107_ = stack[5].m_obj;
lean_object* v___y_108_ = stack[6].m_obj;
lean_object* v___y_109_ = stack[7].m_obj;
lean_object* v___y_110_ = stack[8].m_obj;
lean_object* v_res_113_;
v_res_113_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0(v_cls_102_, v_msg_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
stack->m_obj
 = v_res_113_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___boxed(lean_object* v_cls_114_, lean_object* v_msg_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0(v_cls_114_, v_msg_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
return v_res_124_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_135_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3));
v___x_136_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5));
v___x_137_ = l_Lean_Name_append(v___x_136_, v___x_135_);
return v___x_137_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7));
v___x_140_ = l_Lean_stringToMessageData(v___x_139_);
return v___x_140_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9));
v___x_143_ = l_Lean_stringToMessageData(v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11));
v___x_146_ = l_Lean_stringToMessageData(v___x_145_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13));
v___x_149_ = l_Lean_stringToMessageData(v___x_148_);
return v___x_149_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16));
v___x_153_ = l_Lean_stringToMessageData(v___x_152_);
return v___x_153_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19));
v___x_160_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5));
v___x_161_ = l_Lean_Name_append(v___x_160_, v___x_159_);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23));
v___x_170_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5));
v___x_171_ = l_Lean_Name_append(v___x_170_, v___x_169_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__25));
v___x_174_ = l_Lean_stringToMessageData(v___x_173_);
return v___x_174_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__27(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = lean_unsigned_to_nat(2u);
v___x_176_ = lean_nat_to_int(v___x_175_);
return v___x_176_;
}
}
lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f(lean_object* v_decl_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_toSignature_186_; lean_object* v_value_187_; uint8_t v_recursive_188_; lean_object* v_inlineAttr_x3f_189_; lean_object* v___y_191_; lean_object* v___y_192_; lean_object* v___y_193_; lean_object* v___y_194_; lean_object* v___y_195_; lean_object* v___y_196_; 
v_toSignature_186_ = lean_ctor_get(v_decl_177_, 0);
lean_inc_ref(v_toSignature_186_);
v_value_187_ = lean_ctor_get(v_decl_177_, 1);
lean_inc_ref(v_value_187_);
v_recursive_188_ = lean_ctor_get_uint8(v_decl_177_, sizeof(void*)*3);
v_inlineAttr_x3f_189_ = lean_ctor_get(v_decl_177_, 2);
lean_inc(v_inlineAttr_x3f_189_);
if (lean_obj_tag(v_value_187_) == 0)
{
lean_object* v_code_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_434_; 
v_code_250_ = lean_ctor_get(v_value_187_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v_value_187_);
if (v_isSharedCheck_434_ == 0)
{
v___x_252_ = v_value_187_;
v_isShared_253_ = v_isSharedCheck_434_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_code_250_);
lean_dec(v_value_187_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_434_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
uint8_t v___x_254_; lean_object* v___x_255_; 
v___x_254_ = 0;
lean_inc_ref(v_code_250_);
v___x_255_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(v_code_250_, v___x_254_, v_a_179_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_toCold_256_; lean_object* v_options_257_; lean_object* v_inheritedTraceOptions_258_; uint8_t v_hasTrace_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___y_263_; uint8_t v___y_264_; lean_object* v___y_265_; lean_object* v___y_266_; lean_object* v___y_267_; uint8_t v___y_310_; lean_object* v___y_311_; 
lean_dec_ref_known(v___x_255_, 1);
v_toCold_256_ = lean_ctor_get(v_a_183_, 0);
v_options_257_ = lean_ctor_get(v_toCold_256_, 2);
v_inheritedTraceOptions_258_ = lean_ctor_get(v_toCold_256_, 11);
v_hasTrace_259_ = lean_ctor_get_uint8(v_options_257_, sizeof(void*)*1);
v___x_260_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0));
v___x_261_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1));
if (v_hasTrace_259_ == 0)
{
goto v___jp_368_;
}
else
{
lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_394_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23));
v___x_395_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24);
v___x_396_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_258_, v_options_257_, v___x_395_);
if (v___x_396_ == 0)
{
goto v___jp_368_;
}
else
{
lean_object* v___x_397_; lean_object* v_funDeclInfoMap_398_; lean_object* v___x_399_; 
v___x_397_ = lean_st_ref_get(v_a_179_);
v_funDeclInfoMap_398_ = lean_ctor_get(v___x_397_, 3);
lean_inc_ref(v_funDeclInfoMap_398_);
lean_dec(v___x_397_);
v___x_399_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(v_funDeclInfoMap_398_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
lean_dec_ref(v_funDeclInfoMap_398_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v_name_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_a_400_);
lean_dec_ref_known(v___x_399_, 1);
v_name_401_ = lean_ctor_get(v_toSignature_186_, 0);
lean_inc(v_name_401_);
v___x_402_ = l_Lean_MessageData_ofName(v_name_401_);
v___x_403_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26);
v___x_404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_402_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
v___x_405_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__27, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__27_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__27);
v___x_406_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v_a_400_);
v___x_407_ = l_Lean_MessageData_ofFormat(v___x_406_);
v___x_408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_404_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v___x_394_, v___x_408_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_dec_ref_known(v___x_409_, 1);
goto v___jp_368_;
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_del_object(v___x_252_);
lean_dec_ref(v_code_250_);
lean_dec(v_inlineAttr_x3f_189_);
lean_dec_ref(v_toSignature_186_);
lean_dec_ref(v_decl_177_);
v_a_410_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_409_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_del_object(v___x_252_);
lean_dec_ref(v_code_250_);
lean_dec(v_inlineAttr_x3f_189_);
lean_dec_ref(v_toSignature_186_);
lean_dec_ref(v_decl_177_);
v_a_418_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_399_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_399_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
v___jp_262_:
{
if (v_hasTrace_259_ == 0)
{
lean_dec(v___y_267_);
lean_dec(v___y_265_);
lean_dec(v___y_263_);
lean_del_object(v___x_252_);
v___y_191_ = v___y_266_;
v___y_192_ = v_a_179_;
v___y_193_ = v_a_181_;
v___y_194_ = v_a_182_;
v___y_195_ = v_a_183_;
v___y_196_ = v_a_184_;
goto v___jp_190_;
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_268_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3));
v___x_269_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6);
v___x_270_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_258_, v_options_257_, v___x_269_);
if (v___x_270_ == 0)
{
lean_dec(v___y_267_);
lean_dec(v___y_265_);
lean_dec(v___y_263_);
lean_del_object(v___x_252_);
v___y_191_ = v___y_266_;
v___y_192_ = v_a_179_;
v___y_193_ = v_a_181_;
v___y_194_ = v_a_182_;
v___y_195_ = v_a_183_;
v___y_196_ = v_a_184_;
goto v___jp_190_;
}
else
{
lean_object* v_name_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
v_name_271_ = lean_ctor_get(v_toSignature_186_, 0);
lean_inc(v_name_271_);
v___x_272_ = l_Lean_MessageData_ofName(v_name_271_);
v___x_273_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8);
v___x_274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_272_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = l_Lean_Compiler_LCNF_Code_size(v___y_264_, v___y_266_);
v___x_276_ = l_Nat_reprFast(v___x_275_);
if (v_isShared_253_ == 0)
{
lean_ctor_set_tag(v___x_252_, 3);
lean_ctor_set(v___x_252_, 0, v___x_276_);
v___x_278_ = v___x_252_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_276_);
v___x_278_ = v_reuseFailAlloc_308_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_279_ = l_Lean_MessageData_ofFormat(v___x_278_);
v___x_280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_274_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10);
v___x_282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_280_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = l_Nat_reprFast(v___y_265_);
v___x_284_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
v___x_285_ = l_Lean_MessageData_ofFormat(v___x_284_);
v___x_286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_282_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12);
v___x_288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = l_Nat_reprFast(v___y_267_);
v___x_290_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
v___x_291_ = l_Lean_MessageData_ofFormat(v___x_290_);
v___x_292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_288_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14);
v___x_294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_292_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = l_Nat_reprFast(v___y_263_);
v___x_296_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
v___x_297_ = l_Lean_MessageData_ofFormat(v___x_296_);
v___x_298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_294_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v___x_268_, v___x_298_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_dec_ref_known(v___x_299_, 1);
v___y_191_ = v___y_266_;
v___y_192_ = v_a_179_;
v___y_193_ = v_a_181_;
v___y_194_ = v_a_182_;
v___y_195_ = v_a_183_;
v___y_196_ = v_a_184_;
goto v___jp_190_;
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
lean_dec_ref(v___y_266_);
lean_dec(v_inlineAttr_x3f_189_);
lean_dec_ref(v_toSignature_186_);
v_a_300_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_299_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_299_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
}
}
v___jp_309_:
{
lean_object* v___x_312_; 
lean_inc_ref(v_a_183_);
v___x_312_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_250_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; lean_object* v___x_314_; lean_object* v_binderRenaming_315_; lean_object* v_visited_316_; lean_object* v_inline_317_; lean_object* v_inlineLocal_318_; lean_object* v___x_319_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_a_313_);
lean_dec_ref_known(v___x_312_, 1);
v___x_314_ = lean_st_ref_get(v_a_179_);
v_binderRenaming_315_ = lean_ctor_get(v___x_314_, 2);
lean_inc(v_binderRenaming_315_);
v_visited_316_ = lean_ctor_get(v___x_314_, 4);
lean_inc(v_visited_316_);
v_inline_317_ = lean_ctor_get(v___x_314_, 5);
lean_inc(v_inline_317_);
v_inlineLocal_318_ = lean_ctor_get(v___x_314_, 6);
lean_inc(v_inlineLocal_318_);
lean_dec(v___x_314_);
v___x_319_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v___y_310_, v_a_313_, v_binderRenaming_315_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
lean_dec(v_binderRenaming_315_);
if (lean_obj_tag(v___x_319_) == 0)
{
if (v_hasTrace_259_ == 0)
{
lean_object* v_a_320_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_a_320_);
lean_dec_ref_known(v___x_319_, 1);
v___y_263_ = v_inlineLocal_318_;
v___y_264_ = v___y_310_;
v___y_265_ = v_visited_316_;
v___y_266_ = v_a_320_;
v___y_267_ = v_inline_317_;
goto v___jp_262_;
}
else
{
lean_object* v_a_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v_a_321_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_a_321_);
lean_dec_ref_known(v___x_319_, 1);
v___x_322_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15));
lean_inc_ref(v___y_311_);
v___x_323_ = l_Lean_Name_mkStr4(v___x_260_, v___x_261_, v___y_311_, v___x_322_);
v___x_324_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5));
lean_inc(v___x_323_);
v___x_325_ = l_Lean_Name_append(v___x_324_, v___x_323_);
v___x_326_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_258_, v_options_257_, v___x_325_);
lean_dec(v___x_325_);
if (v___x_326_ == 0)
{
lean_dec(v___x_323_);
v___y_263_ = v_inlineLocal_318_;
v___y_264_ = v___y_310_;
v___y_265_ = v_visited_316_;
v___y_266_ = v_a_321_;
v___y_267_ = v_inline_317_;
goto v___jp_262_;
}
else
{
lean_object* v___x_327_; 
lean_inc(v_a_321_);
v___x_327_ = l_Lean_Compiler_LCNF_ppCode(v___y_310_, v_a_321_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_328_; lean_object* v_name_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v_a_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_a_328_);
lean_dec_ref_known(v___x_327_, 1);
v_name_329_ = lean_ctor_get(v_toSignature_186_, 0);
lean_inc(v_name_329_);
v___x_330_ = l_Lean_MessageData_ofName(v_name_329_);
v___x_331_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17);
v___x_332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_330_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = l_Lean_MessageData_ofFormat(v_a_328_);
v___x_334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_332_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v___x_323_, v___x_334_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_dec_ref_known(v___x_335_, 1);
v___y_263_ = v_inlineLocal_318_;
v___y_264_ = v___y_310_;
v___y_265_ = v_visited_316_;
v___y_266_ = v_a_321_;
v___y_267_ = v_inline_317_;
goto v___jp_262_;
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
lean_dec(v_a_321_);
lean_dec(v_inlineLocal_318_);
lean_dec(v_inline_317_);
lean_dec(v_visited_316_);
lean_del_object(v___x_252_);
lean_dec(v_inlineAttr_x3f_189_);
lean_dec_ref(v_toSignature_186_);
v_a_336_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_335_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_335_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec(v___x_323_);
lean_dec(v_a_321_);
lean_dec(v_inlineLocal_318_);
lean_dec(v_inline_317_);
lean_dec(v_visited_316_);
lean_del_object(v___x_252_);
lean_dec(v_inlineAttr_x3f_189_);
lean_dec_ref(v_toSignature_186_);
v_a_344_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_327_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_327_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
}
}
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
lean_dec(v_inlineLocal_318_);
lean_dec(v_inline_317_);
lean_dec(v_visited_316_);
lean_del_object(v___x_252_);
lean_dec(v_inlineAttr_x3f_189_);
lean_dec_ref(v_toSignature_186_);
v_a_352_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_319_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_319_);
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
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
lean_del_object(v___x_252_);
lean_dec(v_inlineAttr_x3f_189_);
lean_dec_ref(v_toSignature_186_);
v_a_360_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_312_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_312_);
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
v___jp_368_:
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18));
v___x_370_ = 0;
if (v_hasTrace_259_ == 0)
{
lean_dec_ref(v_decl_177_);
v___y_310_ = v___x_370_;
v___y_311_ = v___x_369_;
goto v___jp_309_;
}
else
{
lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_371_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19));
v___x_372_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20);
v___x_373_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_258_, v_options_257_, v___x_372_);
if (v___x_373_ == 0)
{
lean_dec_ref(v_decl_177_);
v___y_310_ = v___x_370_;
v___y_311_ = v___x_369_;
goto v___jp_309_;
}
else
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_Compiler_LCNF_ppDecl(v___x_370_, v_decl_177_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_a_375_);
lean_dec_ref_known(v___x_374_, 1);
v___x_376_ = l_Lean_MessageData_ofFormat(v_a_375_);
v___x_377_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v___x_371_, v___x_376_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_dec_ref_known(v___x_377_, 1);
v___y_310_ = v___x_370_;
v___y_311_ = v___x_369_;
goto v___jp_309_;
}
else
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_385_; 
lean_del_object(v___x_252_);
lean_dec_ref(v_code_250_);
lean_dec(v_inlineAttr_x3f_189_);
lean_dec_ref(v_toSignature_186_);
v_a_378_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_385_ == 0)
{
v___x_380_ = v___x_377_;
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_377_);
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
lean_del_object(v___x_252_);
lean_dec_ref(v_code_250_);
lean_dec(v_inlineAttr_x3f_189_);
lean_dec_ref(v_toSignature_186_);
v_a_386_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_374_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_374_);
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
}
}
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_del_object(v___x_252_);
lean_dec_ref(v_code_250_);
lean_dec(v_inlineAttr_x3f_189_);
lean_dec_ref(v_toSignature_186_);
lean_dec_ref(v_decl_177_);
v_a_426_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_255_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_255_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
else
{
lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec(v_inlineAttr_x3f_189_);
lean_dec_ref(v_value_187_);
lean_dec_ref(v_toSignature_186_);
lean_dec_ref(v_decl_177_);
v___x_435_ = lean_box(0);
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
return v___x_436_;
}
v___jp_190_:
{
lean_object* v___x_197_; 
lean_inc_ref(v___y_191_);
v___x_197_ = l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(v___y_191_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_241_; 
v_a_198_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_241_ == 0)
{
v___x_200_ = v___x_197_;
v_isShared_201_ = v_isSharedCheck_241_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_197_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_241_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
if (lean_obj_tag(v_a_198_) == 1)
{
lean_object* v_val_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_228_; 
lean_del_object(v___x_200_);
lean_dec_ref(v___y_191_);
v_val_202_ = lean_ctor_get(v_a_198_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v_a_198_);
if (v_isSharedCheck_228_ == 0)
{
v___x_204_ = v_a_198_;
v_isShared_205_ = v_isSharedCheck_228_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_val_202_);
lean_dec(v_a_198_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_228_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_206_, 0, v_val_202_);
v___x_207_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_207_, 0, v_toSignature_186_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
lean_ctor_set(v___x_207_, 2, v_inlineAttr_x3f_189_);
lean_ctor_set_uint8(v___x_207_, sizeof(void*)*3, v_recursive_188_);
v___x_208_ = l_Lean_Compiler_LCNF_Decl_reduceJpArity(v___x_207_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_219_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_219_ == 0)
{
v___x_211_ = v___x_208_;
v_isShared_212_ = v_isSharedCheck_219_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_208_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_219_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v_a_209_);
v___x_214_ = v___x_204_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_a_209_);
v___x_214_ = v_reuseFailAlloc_218_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_216_; 
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_214_);
v___x_216_ = v___x_211_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
else
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
lean_del_object(v___x_204_);
v_a_220_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_227_ == 0)
{
v___x_222_ = v___x_208_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_208_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_220_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
}
else
{
lean_object* v___x_229_; uint8_t v_simplified_230_; 
lean_dec(v_a_198_);
v___x_229_ = lean_st_ref_get(v___y_192_);
v_simplified_230_ = lean_ctor_get_uint8(v___x_229_, sizeof(void*)*7);
lean_dec(v___x_229_);
if (v_simplified_230_ == 0)
{
lean_object* v___x_231_; lean_object* v___x_233_; 
lean_dec_ref(v___y_191_);
lean_dec(v_inlineAttr_x3f_189_);
lean_dec_ref(v_toSignature_186_);
v___x_231_ = lean_box(0);
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 0, v___x_231_);
v___x_233_ = v___x_200_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
else
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___y_191_);
v___x_236_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_236_, 0, v_toSignature_186_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
lean_ctor_set(v___x_236_, 2, v_inlineAttr_x3f_189_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*3, v_recursive_188_);
v___x_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 0, v___x_237_);
v___x_239_ = v___x_200_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
lean_dec_ref(v___y_191_);
lean_dec(v_inlineAttr_x3f_189_);
lean_dec_ref(v_toSignature_186_);
v_a_242_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_197_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_197_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Decl_simp_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_177_ = stack[0].m_obj;
lean_object* v_a_178_ = stack[1].m_obj;
lean_object* v_a_179_ = stack[2].m_obj;
lean_object* v_a_180_ = stack[3].m_obj;
lean_object* v_a_181_ = stack[4].m_obj;
lean_object* v_a_182_ = stack[5].m_obj;
lean_object* v_a_183_ = stack[6].m_obj;
lean_object* v_a_184_ = stack[7].m_obj;
lean_object* v_res_437_;
v_res_437_ = l_Lean_Compiler_LCNF_Decl_simp_x3f(v_decl_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
stack->m_obj
 = v_res_437_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___boxed(lean_object* v_decl_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_Compiler_LCNF_Decl_simp_x3f(v_decl_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec_ref(v_a_441_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
return v_res_447_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__0);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
return v___x_449_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_450_ = lean_box(0);
v___x_451_ = lean_unsigned_to_nat(16u);
v___x_452_ = lean_mk_array(v___x_451_, v___x_450_);
return v___x_452_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1, &l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1);
v___x_454_ = lean_unsigned_to_nat(0u);
v___x_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
lean_ctor_set(v___x_455_, 1, v___x_453_);
return v___x_455_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3(void){
_start:
{
lean_object* v___x_456_; uint8_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = 0;
v___x_458_ = lean_box(1);
v___x_459_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2, &l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2_once, _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2);
v___x_460_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_460_, 0, v___x_459_);
lean_ctor_set(v___x_460_, 1, v___x_458_);
lean_ctor_set(v___x_460_, 2, v___x_458_);
lean_ctor_set(v___x_460_, 3, v___x_459_);
lean_ctor_set(v___x_460_, 4, v___x_456_);
lean_ctor_set(v___x_460_, 5, v___x_456_);
lean_ctor_set(v___x_460_, 6, v___x_456_);
lean_ctor_set_uint8(v___x_460_, sizeof(void*)*7, v___x_457_);
return v___x_460_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0, &l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0);
v___x_462_ = lean_box(1);
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set(v___x_463_, 1, v___x_461_);
return v___x_463_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go(lean_object* v_decl_464_, lean_object* v_config_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_toSignature_471_; lean_object* v_name_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v_toSignature_471_ = lean_ctor_get(v_decl_464_, 0);
v_name_472_ = lean_ctor_get(v_toSignature_471_, 0);
v___x_473_ = lean_box(0);
v___x_474_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0, &l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0);
lean_inc_ref(v_config_465_);
lean_inc(v_name_472_);
v___x_475_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_475_, 0, v_name_472_);
lean_ctor_set(v___x_475_, 1, v_config_465_);
lean_ctor_set(v___x_475_, 2, v___x_473_);
lean_ctor_set(v___x_475_, 3, v___x_474_);
v___x_476_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3, &l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3);
v___x_477_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4, &l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4_once, _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4);
v___x_478_ = lean_st_mk_ref(v___x_476_);
lean_inc_ref(v_decl_464_);
v___x_479_ = l_Lean_Compiler_LCNF_Decl_simp_x3f(v_decl_464_, v___x_475_, v___x_478_, v___x_477_, v_a_466_, v_a_467_, v_a_468_, v_a_469_);
lean_dec_ref_known(v___x_475_, 4);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_490_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_490_ == 0)
{
v___x_482_ = v___x_479_;
v_isShared_483_ = v_isSharedCheck_490_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_490_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; 
v___x_484_ = lean_st_ref_get(v___x_478_);
lean_dec(v___x_478_);
lean_dec(v___x_484_);
if (lean_obj_tag(v_a_480_) == 1)
{
lean_object* v_val_485_; 
lean_del_object(v___x_482_);
lean_dec_ref(v_decl_464_);
v_val_485_ = lean_ctor_get(v_a_480_, 0);
lean_inc(v_val_485_);
lean_dec_ref_known(v_a_480_, 1);
v_decl_464_ = v_val_485_;
goto _start;
}
else
{
lean_object* v___x_488_; 
lean_dec(v_a_480_);
lean_dec_ref(v_config_465_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v_decl_464_);
v___x_488_ = v___x_482_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_decl_464_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec(v___x_478_);
lean_dec_ref(v_config_465_);
lean_dec_ref(v_decl_464_);
v_a_491_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_479_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_479_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_464_ = stack[0].m_obj;
lean_object* v_config_465_ = stack[1].m_obj;
lean_object* v_a_466_ = stack[2].m_obj;
lean_object* v_a_467_ = stack[3].m_obj;
lean_object* v_a_468_ = stack[4].m_obj;
lean_object* v_a_469_ = stack[5].m_obj;
lean_object* v_res_499_;
v_res_499_ = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go(v_decl_464_, v_config_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_);
stack->m_obj
 = v_res_499_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___boxed(lean_object* v_decl_500_, lean_object* v_config_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go(v_decl_500_, v_config_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
lean_dec(v_a_505_);
lean_dec_ref(v_a_504_);
lean_dec(v_a_503_);
lean_dec_ref(v_a_502_);
return v_res_507_;
}
}
lean_object* l_Lean_Compiler_LCNF_Decl_simp(lean_object* v_decl_508_, lean_object* v_config_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v___x_515_; 
lean_inc_ref(v_decl_508_);
v___x_515_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(v_decl_508_, v_a_512_, v_a_513_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; uint8_t v___x_517_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
lean_dec_ref_known(v___x_515_, 1);
v___x_517_ = lean_unbox(v_a_516_);
lean_dec(v_a_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; 
v___x_518_ = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go(v_decl_508_, v_config_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
return v___x_518_;
}
else
{
uint8_t v_implementedBy_519_; uint8_t v_inlineDefs_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_529_; 
v_implementedBy_519_ = lean_ctor_get_uint8(v_config_509_, 2);
v_inlineDefs_520_ = lean_ctor_get_uint8(v_config_509_, 3);
v_isSharedCheck_529_ = !lean_is_exclusive(v_config_509_);
if (v_isSharedCheck_529_ == 0)
{
v___x_522_ = v_config_509_;
v_isShared_523_ = v_isSharedCheck_529_;
goto v_resetjp_521_;
}
else
{
lean_dec(v_config_509_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_529_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
uint8_t v___x_524_; lean_object* v___x_526_; 
v___x_524_ = 0;
if (v_isShared_523_ == 0)
{
v___x_526_ = v___x_522_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v_reuseFailAlloc_528_, 2, v_implementedBy_519_);
lean_ctor_set_uint8(v_reuseFailAlloc_528_, 3, v_inlineDefs_520_);
v___x_526_ = v_reuseFailAlloc_528_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_527_; 
lean_ctor_set_uint8(v___x_526_, 0, v___x_524_);
lean_ctor_set_uint8(v___x_526_, 1, v___x_524_);
v___x_527_ = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go(v_decl_508_, v___x_526_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
return v___x_527_;
}
}
}
}
else
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
lean_dec_ref(v_config_509_);
lean_dec_ref(v_decl_508_);
v_a_530_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_515_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_515_);
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
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Decl_simp_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_508_ = stack[0].m_obj;
lean_object* v_config_509_ = stack[1].m_obj;
lean_object* v_a_510_ = stack[2].m_obj;
lean_object* v_a_511_ = stack[3].m_obj;
lean_object* v_a_512_ = stack[4].m_obj;
lean_object* v_a_513_ = stack[5].m_obj;
lean_object* v_res_538_;
v_res_538_ = l_Lean_Compiler_LCNF_Decl_simp(v_decl_508_, v_config_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
stack->m_obj
 = v_res_538_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp___boxed(lean_object* v_decl_539_, lean_object* v_config_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Compiler_LCNF_Decl_simp(v_decl_539_, v_config_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
return v_res_546_;
}
}
lean_object* l_Lean_Compiler_LCNF_simp___lam__0(lean_object* v_config_547_, lean_object* v_x_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_Compiler_LCNF_Decl_simp(v_x_548_, v_config_547_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
return v___x_554_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_simp___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_547_ = stack[0].m_obj;
lean_object* v_x_548_ = stack[1].m_obj;
lean_object* v___y_549_ = stack[2].m_obj;
lean_object* v___y_550_ = stack[3].m_obj;
lean_object* v___y_551_ = stack[4].m_obj;
lean_object* v___y_552_ = stack[5].m_obj;
lean_object* v_res_555_;
v_res_555_ = l_Lean_Compiler_LCNF_simp___lam__0(v_config_547_, v_x_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
stack->m_obj
 = v_res_555_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___lam__0___boxed(lean_object* v_config_556_, lean_object* v_x_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_Compiler_LCNF_simp___lam__0(v_config_556_, v_x_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
return v_res_563_;
}
}
lean_object* l_Lean_Compiler_LCNF_simp___lam__1(uint8_t v_phase_566_, lean_object* v___f_567_, lean_object* v_occurrence_568_, lean_object* v_h_569_){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l_Lean_Compiler_LCNF_simp___lam__1___closed__0));
v___x_571_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_570_, v_phase_566_, v___f_567_, v_occurrence_568_);
return v___x_571_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_simp___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_566_ = stack[0].m_num;
lean_object* v___f_567_ = stack[1].m_obj;
lean_object* v_occurrence_568_ = stack[2].m_obj;
lean_object* v_res_572_;
v_res_572_ = l_Lean_Compiler_LCNF_simp___lam__1(v_phase_566_, v___f_567_, v_occurrence_568_, lean_box(0));
stack->m_obj
 = v_res_572_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___lam__1___boxed(lean_object* v_phase_573_, lean_object* v___f_574_, lean_object* v_occurrence_575_, lean_object* v_h_576_){
_start:
{
uint8_t v_phase_boxed_577_; lean_object* v_res_578_; 
v_phase_boxed_577_ = lean_unbox(v_phase_573_);
v_res_578_ = l_Lean_Compiler_LCNF_simp___lam__1(v_phase_boxed_577_, v___f_574_, v_occurrence_575_, v_h_576_);
return v_res_578_;
}
}
lean_object* l_Lean_Compiler_LCNF_simp(lean_object* v_config_579_, lean_object* v_occurrence_580_, uint8_t v_phase_581_){
_start:
{
lean_object* v___f_582_; lean_object* v___x_583_; lean_object* v___f_584_; lean_object* v___x_585_; uint8_t v___x_586_; lean_object* v___x_587_; 
v___f_582_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_simp___lam__0___boxed), 7, 1);
lean_closure_set(v___f_582_, 0, v_config_579_);
v___x_583_ = lean_box(v_phase_581_);
v___f_584_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_simp___lam__1___boxed), 4, 3);
lean_closure_set(v___f_584_, 0, v___x_583_);
lean_closure_set(v___f_584_, 1, v___f_582_);
lean_closure_set(v___f_584_, 2, v_occurrence_580_);
v___x_585_ = l_Lean_Compiler_LCNF_instInhabitedPass;
v___x_586_ = 0;
v___x_587_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___x_585_, v_phase_581_, v___x_586_, v___f_584_);
return v___x_587_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_simp_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_579_ = stack[0].m_obj;
lean_object* v_occurrence_580_ = stack[1].m_obj;
uint8_t v_phase_581_ = stack[2].m_num;
lean_object* v_res_588_;
v_res_588_ = l_Lean_Compiler_LCNF_simp(v_config_579_, v_occurrence_580_, v_phase_581_);
stack->m_obj
 = v_res_588_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___boxed(lean_object* v_config_589_, lean_object* v_occurrence_590_, lean_object* v_phase_591_){
_start:
{
uint8_t v_phase_boxed_592_; lean_object* v_res_593_; 
v_phase_boxed_592_ = lean_unbox(v_phase_591_);
v_res_593_ = l_Lean_Compiler_LCNF_simp(v_config_589_, v_occurrence_590_, v_phase_boxed_592_);
return v_res_593_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_668_; uint8_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_668_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_));
v___x_669_ = 1;
v___x_670_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_));
v___x_671_ = l_Lean_registerTraceClass(v___x_668_, v___x_669_, v___x_670_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v___x_672_; uint8_t v___x_673_; lean_object* v___x_674_; 
lean_dec_ref_known(v___x_671_, 1);
v___x_672_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3));
v___x_673_ = 0;
v___x_674_ = l_Lean_registerTraceClass(v___x_672_, v___x_673_, v___x_670_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec_ref_known(v___x_674_, 1);
v___x_675_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19));
v___x_676_ = l_Lean_registerTraceClass(v___x_675_, v___x_673_, v___x_670_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; 
lean_dec_ref_known(v___x_676_, 1);
v___x_677_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_));
v___x_678_ = l_Lean_registerTraceClass(v___x_677_, v___x_673_, v___x_670_);
return v___x_678_;
}
else
{
return v___x_676_;
}
}
else
{
return v___x_674_;
}
}
else
{
return v___x_671_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_679_;
v_res_679_ = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
stack->m_obj
 = v_res_679_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2____boxed(lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
return v_res_681_;
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

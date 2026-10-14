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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(lean_object* v_cls_13_, lean_object* v_msg_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___boxed(lean_object* v_cls_93_, lean_object* v_msg_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v_cls_93_, v_msg_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0(lean_object* v_cls_101_, lean_object* v_msg_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v_cls_101_, v_msg_102_, v___y_106_, v___y_107_, v___y_108_, v___y_109_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___boxed(lean_object* v_cls_112_, lean_object* v_msg_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0(v_cls_112_, v_msg_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
return v_res_122_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3));
v___x_134_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5));
v___x_135_ = l_Lean_Name_append(v___x_134_, v___x_133_);
return v___x_135_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7));
v___x_138_ = l_Lean_stringToMessageData(v___x_137_);
return v___x_138_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9));
v___x_141_ = l_Lean_stringToMessageData(v___x_140_);
return v___x_141_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11));
v___x_144_ = l_Lean_stringToMessageData(v___x_143_);
return v___x_144_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13));
v___x_147_ = l_Lean_stringToMessageData(v___x_146_);
return v___x_147_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16));
v___x_151_ = l_Lean_stringToMessageData(v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19));
v___x_158_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5));
v___x_159_ = l_Lean_Name_append(v___x_158_, v___x_157_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23));
v___x_168_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5));
v___x_169_ = l_Lean_Name_append(v___x_168_, v___x_167_);
return v___x_169_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__25));
v___x_172_ = l_Lean_stringToMessageData(v___x_171_);
return v___x_172_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__27(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_unsigned_to_nat(2u);
v___x_174_ = lean_nat_to_int(v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f(lean_object* v_decl_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_toSignature_184_; lean_object* v_value_185_; uint8_t v_recursive_186_; lean_object* v_inlineAttr_x3f_187_; lean_object* v___y_189_; lean_object* v___y_190_; lean_object* v___y_191_; lean_object* v___y_192_; lean_object* v___y_193_; lean_object* v___y_194_; 
v_toSignature_184_ = lean_ctor_get(v_decl_175_, 0);
lean_inc_ref(v_toSignature_184_);
v_value_185_ = lean_ctor_get(v_decl_175_, 1);
lean_inc_ref(v_value_185_);
v_recursive_186_ = lean_ctor_get_uint8(v_decl_175_, sizeof(void*)*3);
v_inlineAttr_x3f_187_ = lean_ctor_get(v_decl_175_, 2);
lean_inc(v_inlineAttr_x3f_187_);
if (lean_obj_tag(v_value_185_) == 0)
{
lean_object* v_code_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_432_; 
v_code_248_ = lean_ctor_get(v_value_185_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v_value_185_);
if (v_isSharedCheck_432_ == 0)
{
v___x_250_ = v_value_185_;
v_isShared_251_ = v_isSharedCheck_432_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_code_248_);
lean_dec(v_value_185_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_432_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
uint8_t v___x_252_; lean_object* v___x_253_; 
v___x_252_ = 0;
lean_inc_ref(v_code_248_);
v___x_253_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(v_code_248_, v___x_252_, v_a_177_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_toCold_254_; lean_object* v_options_255_; lean_object* v_inheritedTraceOptions_256_; uint8_t v_hasTrace_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___y_261_; uint8_t v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_265_; uint8_t v___y_308_; lean_object* v___y_309_; 
lean_dec_ref_known(v___x_253_, 1);
v_toCold_254_ = lean_ctor_get(v_a_181_, 0);
v_options_255_ = lean_ctor_get(v_toCold_254_, 2);
v_inheritedTraceOptions_256_ = lean_ctor_get(v_toCold_254_, 11);
v_hasTrace_257_ = lean_ctor_get_uint8(v_options_255_, sizeof(void*)*1);
v___x_258_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0));
v___x_259_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1));
if (v_hasTrace_257_ == 0)
{
goto v___jp_366_;
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_392_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23));
v___x_393_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24);
v___x_394_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_256_, v_options_255_, v___x_393_);
if (v___x_394_ == 0)
{
goto v___jp_366_;
}
else
{
lean_object* v___x_395_; lean_object* v_funDeclInfoMap_396_; lean_object* v___x_397_; 
v___x_395_ = lean_st_ref_get(v_a_177_);
v_funDeclInfoMap_396_ = lean_ctor_get(v___x_395_, 3);
lean_inc_ref(v_funDeclInfoMap_396_);
lean_dec(v___x_395_);
v___x_397_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(v_funDeclInfoMap_396_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
lean_dec_ref(v_funDeclInfoMap_396_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v_name_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_a_398_);
lean_dec_ref_known(v___x_397_, 1);
v_name_399_ = lean_ctor_get(v_toSignature_184_, 0);
lean_inc(v_name_399_);
v___x_400_ = l_Lean_MessageData_ofName(v_name_399_);
v___x_401_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26);
v___x_402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_400_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__27, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__27_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__27);
v___x_404_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v_a_398_);
v___x_405_ = l_Lean_MessageData_ofFormat(v___x_404_);
v___x_406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_402_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v___x_392_, v___x_406_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_dec_ref_known(v___x_407_, 1);
goto v___jp_366_;
}
else
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
lean_del_object(v___x_250_);
lean_dec_ref(v_code_248_);
lean_dec(v_inlineAttr_x3f_187_);
lean_dec_ref(v_toSignature_184_);
lean_dec_ref(v_decl_175_);
v_a_408_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_407_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_408_);
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
else
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
lean_del_object(v___x_250_);
lean_dec_ref(v_code_248_);
lean_dec(v_inlineAttr_x3f_187_);
lean_dec_ref(v_toSignature_184_);
lean_dec_ref(v_decl_175_);
v_a_416_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___x_397_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_397_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
}
v___jp_260_:
{
if (v_hasTrace_257_ == 0)
{
lean_dec(v___y_265_);
lean_dec(v___y_263_);
lean_dec(v___y_261_);
lean_del_object(v___x_250_);
v___y_189_ = v___y_264_;
v___y_190_ = v_a_177_;
v___y_191_ = v_a_179_;
v___y_192_ = v_a_180_;
v___y_193_ = v_a_181_;
v___y_194_ = v_a_182_;
goto v___jp_188_;
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_266_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3));
v___x_267_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6);
v___x_268_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_256_, v_options_255_, v___x_267_);
if (v___x_268_ == 0)
{
lean_dec(v___y_265_);
lean_dec(v___y_263_);
lean_dec(v___y_261_);
lean_del_object(v___x_250_);
v___y_189_ = v___y_264_;
v___y_190_ = v_a_177_;
v___y_191_ = v_a_179_;
v___y_192_ = v_a_180_;
v___y_193_ = v_a_181_;
v___y_194_ = v_a_182_;
goto v___jp_188_;
}
else
{
lean_object* v_name_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
v_name_269_ = lean_ctor_get(v_toSignature_184_, 0);
lean_inc(v_name_269_);
v___x_270_ = l_Lean_MessageData_ofName(v_name_269_);
v___x_271_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8);
v___x_272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = l_Lean_Compiler_LCNF_Code_size(v___y_262_, v___y_264_);
v___x_274_ = l_Nat_reprFast(v___x_273_);
if (v_isShared_251_ == 0)
{
lean_ctor_set_tag(v___x_250_, 3);
lean_ctor_set(v___x_250_, 0, v___x_274_);
v___x_276_ = v___x_250_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_306_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_277_ = l_Lean_MessageData_ofFormat(v___x_276_);
v___x_278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_272_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10);
v___x_280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_278_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = l_Nat_reprFast(v___y_263_);
v___x_282_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
v___x_283_ = l_Lean_MessageData_ofFormat(v___x_282_);
v___x_284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_280_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12);
v___x_286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = l_Nat_reprFast(v___y_265_);
v___x_288_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
v___x_289_ = l_Lean_MessageData_ofFormat(v___x_288_);
v___x_290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_286_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14);
v___x_292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = l_Nat_reprFast(v___y_261_);
v___x_294_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
v___x_295_ = l_Lean_MessageData_ofFormat(v___x_294_);
v___x_296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_292_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v___x_266_, v___x_296_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_dec_ref_known(v___x_297_, 1);
v___y_189_ = v___y_264_;
v___y_190_ = v_a_177_;
v___y_191_ = v_a_179_;
v___y_192_ = v_a_180_;
v___y_193_ = v_a_181_;
v___y_194_ = v_a_182_;
goto v___jp_188_;
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_dec_ref(v___y_264_);
lean_dec(v_inlineAttr_x3f_187_);
lean_dec_ref(v_toSignature_184_);
v_a_298_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_297_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_297_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
}
}
}
v___jp_307_:
{
lean_object* v___x_310_; 
lean_inc_ref(v_a_181_);
v___x_310_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_248_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v___x_312_; lean_object* v_binderRenaming_313_; lean_object* v_visited_314_; lean_object* v_inline_315_; lean_object* v_inlineLocal_316_; lean_object* v___x_317_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_311_);
lean_dec_ref_known(v___x_310_, 1);
v___x_312_ = lean_st_ref_get(v_a_177_);
v_binderRenaming_313_ = lean_ctor_get(v___x_312_, 2);
lean_inc(v_binderRenaming_313_);
v_visited_314_ = lean_ctor_get(v___x_312_, 4);
lean_inc(v_visited_314_);
v_inline_315_ = lean_ctor_get(v___x_312_, 5);
lean_inc(v_inline_315_);
v_inlineLocal_316_ = lean_ctor_get(v___x_312_, 6);
lean_inc(v_inlineLocal_316_);
lean_dec(v___x_312_);
v___x_317_ = l_Lean_Compiler_LCNF_Code_applyRenaming(v___y_308_, v_a_311_, v_binderRenaming_313_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
lean_dec(v_binderRenaming_313_);
if (lean_obj_tag(v___x_317_) == 0)
{
if (v_hasTrace_257_ == 0)
{
lean_object* v_a_318_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_a_318_);
lean_dec_ref_known(v___x_317_, 1);
v___y_261_ = v_inlineLocal_316_;
v___y_262_ = v___y_308_;
v___y_263_ = v_visited_314_;
v___y_264_ = v_a_318_;
v___y_265_ = v_inline_315_;
goto v___jp_260_;
}
else
{
lean_object* v_a_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v_a_319_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_a_319_);
lean_dec_ref_known(v___x_317_, 1);
v___x_320_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15));
lean_inc_ref(v___y_309_);
v___x_321_ = l_Lean_Name_mkStr4(v___x_258_, v___x_259_, v___y_309_, v___x_320_);
v___x_322_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5));
lean_inc(v___x_321_);
v___x_323_ = l_Lean_Name_append(v___x_322_, v___x_321_);
v___x_324_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_256_, v_options_255_, v___x_323_);
lean_dec(v___x_323_);
if (v___x_324_ == 0)
{
lean_dec(v___x_321_);
v___y_261_ = v_inlineLocal_316_;
v___y_262_ = v___y_308_;
v___y_263_ = v_visited_314_;
v___y_264_ = v_a_319_;
v___y_265_ = v_inline_315_;
goto v___jp_260_;
}
else
{
lean_object* v___x_325_; 
lean_inc(v_a_319_);
v___x_325_ = l_Lean_Compiler_LCNF_ppCode(v___y_308_, v_a_319_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v_name_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_a_326_);
lean_dec_ref_known(v___x_325_, 1);
v_name_327_ = lean_ctor_get(v_toSignature_184_, 0);
lean_inc(v_name_327_);
v___x_328_ = l_Lean_MessageData_ofName(v_name_327_);
v___x_329_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17);
v___x_330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_328_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v___x_331_ = l_Lean_MessageData_ofFormat(v_a_326_);
v___x_332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_330_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v___x_321_, v___x_332_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_dec_ref_known(v___x_333_, 1);
v___y_261_ = v_inlineLocal_316_;
v___y_262_ = v___y_308_;
v___y_263_ = v_visited_314_;
v___y_264_ = v_a_319_;
v___y_265_ = v_inline_315_;
goto v___jp_260_;
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
lean_dec(v_a_319_);
lean_dec(v_inlineLocal_316_);
lean_dec(v_inline_315_);
lean_dec(v_visited_314_);
lean_del_object(v___x_250_);
lean_dec(v_inlineAttr_x3f_187_);
lean_dec_ref(v_toSignature_184_);
v_a_334_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_333_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_333_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
else
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
lean_dec(v___x_321_);
lean_dec(v_a_319_);
lean_dec(v_inlineLocal_316_);
lean_dec(v_inline_315_);
lean_dec(v_visited_314_);
lean_del_object(v___x_250_);
lean_dec(v_inlineAttr_x3f_187_);
lean_dec_ref(v_toSignature_184_);
v_a_342_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_325_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_325_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_342_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec(v_inlineLocal_316_);
lean_dec(v_inline_315_);
lean_dec(v_visited_314_);
lean_del_object(v___x_250_);
lean_dec(v_inlineAttr_x3f_187_);
lean_dec_ref(v_toSignature_184_);
v_a_350_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_317_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_317_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_del_object(v___x_250_);
lean_dec(v_inlineAttr_x3f_187_);
lean_dec_ref(v_toSignature_184_);
v_a_358_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_310_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_310_);
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
v___jp_366_:
{
lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_367_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18));
v___x_368_ = 0;
if (v_hasTrace_257_ == 0)
{
lean_dec_ref(v_decl_175_);
v___y_308_ = v___x_368_;
v___y_309_ = v___x_367_;
goto v___jp_307_;
}
else
{
lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_369_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19));
v___x_370_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20, &l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20_once, _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20);
v___x_371_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_256_, v_options_255_, v___x_370_);
if (v___x_371_ == 0)
{
lean_dec_ref(v_decl_175_);
v___y_308_ = v___x_368_;
v___y_309_ = v___x_367_;
goto v___jp_307_;
}
else
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Compiler_LCNF_ppDecl(v___x_368_, v_decl_175_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_a_373_);
lean_dec_ref_known(v___x_372_, 1);
v___x_374_ = l_Lean_MessageData_ofFormat(v_a_373_);
v___x_375_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v___x_369_, v___x_374_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_dec_ref_known(v___x_375_, 1);
v___y_308_ = v___x_368_;
v___y_309_ = v___x_367_;
goto v___jp_307_;
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_del_object(v___x_250_);
lean_dec_ref(v_code_248_);
lean_dec(v_inlineAttr_x3f_187_);
lean_dec_ref(v_toSignature_184_);
v_a_376_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_375_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_375_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
lean_del_object(v___x_250_);
lean_dec_ref(v_code_248_);
lean_dec(v_inlineAttr_x3f_187_);
lean_dec_ref(v_toSignature_184_);
v_a_384_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_372_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_372_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_del_object(v___x_250_);
lean_dec_ref(v_code_248_);
lean_dec(v_inlineAttr_x3f_187_);
lean_dec_ref(v_toSignature_184_);
lean_dec_ref(v_decl_175_);
v_a_424_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_253_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_253_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
else
{
lean_object* v___x_433_; lean_object* v___x_434_; 
lean_dec(v_inlineAttr_x3f_187_);
lean_dec_ref(v_value_185_);
lean_dec_ref(v_toSignature_184_);
lean_dec_ref(v_decl_175_);
v___x_433_ = lean_box(0);
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
return v___x_434_;
}
v___jp_188_:
{
lean_object* v___x_195_; 
lean_inc_ref(v___y_189_);
v___x_195_ = l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(v___y_189_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_239_; 
v_a_196_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_239_ == 0)
{
v___x_198_ = v___x_195_;
v_isShared_199_ = v_isSharedCheck_239_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_195_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_239_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
if (lean_obj_tag(v_a_196_) == 1)
{
lean_object* v_val_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_226_; 
lean_del_object(v___x_198_);
lean_dec_ref(v___y_189_);
v_val_200_ = lean_ctor_get(v_a_196_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v_a_196_);
if (v_isSharedCheck_226_ == 0)
{
v___x_202_ = v_a_196_;
v_isShared_203_ = v_isSharedCheck_226_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_val_200_);
lean_dec(v_a_196_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_226_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v_val_200_);
v___x_205_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_205_, 0, v_toSignature_184_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
lean_ctor_set(v___x_205_, 2, v_inlineAttr_x3f_187_);
lean_ctor_set_uint8(v___x_205_, sizeof(void*)*3, v_recursive_186_);
v___x_206_ = l_Lean_Compiler_LCNF_Decl_reduceJpArity(v___x_205_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_217_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_217_ == 0)
{
v___x_209_ = v___x_206_;
v_isShared_210_ = v_isSharedCheck_217_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_206_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_217_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 0, v_a_207_);
v___x_212_ = v___x_202_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_216_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_214_; 
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 0, v___x_212_);
v___x_214_ = v___x_209_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_212_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
else
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
lean_del_object(v___x_202_);
v_a_218_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v___x_206_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_206_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
}
else
{
lean_object* v___x_227_; uint8_t v_simplified_228_; 
lean_dec(v_a_196_);
v___x_227_ = lean_st_ref_get(v___y_190_);
v_simplified_228_ = lean_ctor_get_uint8(v___x_227_, sizeof(void*)*7);
lean_dec(v___x_227_);
if (v_simplified_228_ == 0)
{
lean_object* v___x_229_; lean_object* v___x_231_; 
lean_dec_ref(v___y_189_);
lean_dec(v_inlineAttr_x3f_187_);
lean_dec_ref(v_toSignature_184_);
v___x_229_ = lean_box(0);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v___x_229_);
v___x_231_ = v___x_198_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
else
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v___y_189_);
v___x_234_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_234_, 0, v_toSignature_184_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
lean_ctor_set(v___x_234_, 2, v_inlineAttr_x3f_187_);
lean_ctor_set_uint8(v___x_234_, sizeof(void*)*3, v_recursive_186_);
v___x_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v___x_235_);
v___x_237_ = v___x_198_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
lean_dec_ref(v___y_189_);
lean_dec(v_inlineAttr_x3f_187_);
lean_dec_ref(v_toSignature_184_);
v_a_240_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_195_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_195_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___boxed(lean_object* v_decl_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_Compiler_LCNF_Decl_simp_x3f(v_decl_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec_ref(v_a_438_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
return v_res_444_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__0);
v___x_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
return v___x_446_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = lean_box(0);
v___x_448_ = lean_unsigned_to_nat(16u);
v___x_449_ = lean_mk_array(v___x_448_, v___x_447_);
return v___x_449_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_450_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1, &l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1);
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
lean_ctor_set(v___x_452_, 1, v___x_450_);
return v___x_452_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3(void){
_start:
{
lean_object* v___x_453_; uint8_t v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_453_ = lean_unsigned_to_nat(0u);
v___x_454_ = 0;
v___x_455_ = lean_box(1);
v___x_456_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2, &l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2_once, _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2);
v___x_457_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v___x_455_);
lean_ctor_set(v___x_457_, 2, v___x_455_);
lean_ctor_set(v___x_457_, 3, v___x_456_);
lean_ctor_set(v___x_457_, 4, v___x_453_);
lean_ctor_set(v___x_457_, 5, v___x_453_);
lean_ctor_set(v___x_457_, 6, v___x_453_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*7, v___x_454_);
return v___x_457_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0, &l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0);
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
lean_object* v_toSignature_468_; lean_object* v_name_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v_toSignature_468_ = lean_ctor_get(v_decl_461_, 0);
v_name_469_ = lean_ctor_get(v_toSignature_468_, 0);
v___x_470_ = lean_box(0);
v___x_471_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0, &l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0);
lean_inc_ref(v_config_462_);
lean_inc(v_name_469_);
v___x_472_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_472_, 0, v_name_469_);
lean_ctor_set(v___x_472_, 1, v_config_462_);
lean_ctor_set(v___x_472_, 2, v___x_470_);
lean_ctor_set(v___x_472_, 3, v___x_471_);
v___x_473_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3, &l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3);
v___x_474_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4, &l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4_once, _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4);
v___x_475_ = lean_st_mk_ref(v___x_473_);
lean_inc_ref(v_decl_461_);
v___x_476_ = l_Lean_Compiler_LCNF_Decl_simp_x3f(v_decl_461_, v___x_472_, v___x_475_, v___x_474_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
lean_dec_ref_known(v___x_472_, 4);
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
v___x_481_ = lean_st_ref_get(v___x_475_);
lean_dec(v___x_475_);
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
lean_dec(v___x_475_);
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

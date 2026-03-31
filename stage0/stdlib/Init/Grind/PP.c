// Lean compiler output
// Module: Init.Grind.PP
// Imports: public meta import Init.Data.String.Defs public import Init.Grind.Tactics
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
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getNat(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_NodeDef_toCtorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_node__def(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_node__def___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Grind_nodeDefUnexpander___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Grind_nodeDefUnexpander___redArg___closed__0 = (const lean_object*)&l_Lean_Grind_nodeDefUnexpander___redArg___closed__0_value;
static const lean_string_object l_Lean_Grind_nodeDefUnexpander___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Grind_nodeDefUnexpander___redArg___closed__1 = (const lean_object*)&l_Lean_Grind_nodeDefUnexpander___redArg___closed__1_value;
static const lean_string_object l_Lean_Grind_nodeDefUnexpander___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Grind_nodeDefUnexpander___redArg___closed__2 = (const lean_object*)&l_Lean_Grind_nodeDefUnexpander___redArg___closed__2_value;
static const lean_string_object l_Lean_Grind_nodeDefUnexpander___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Grind_nodeDefUnexpander___redArg___closed__3 = (const lean_object*)&l_Lean_Grind_nodeDefUnexpander___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_nodeDefUnexpander___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Grind_nodeDefUnexpander___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value_aux_1),((lean_object*)&l_Lean_Grind_nodeDefUnexpander___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value_aux_2),((lean_object*)&l_Lean_Grind_nodeDefUnexpander___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Grind_nodeDefUnexpander___redArg___closed__4 = (const lean_object*)&l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value;
static const lean_string_object l_Lean_Grind_nodeDefUnexpander___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Grind_nodeDefUnexpander___redArg___closed__5 = (const lean_object*)&l_Lean_Grind_nodeDefUnexpander___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Grind_nodeDefUnexpander___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_nodeDefUnexpander___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Grind_nodeDefUnexpander___redArg___closed__6 = (const lean_object*)&l_Lean_Grind_nodeDefUnexpander___redArg___closed__6_value;
static const lean_string_object l_Lean_Grind_nodeDefUnexpander___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Lean_Grind_nodeDefUnexpander___redArg___closed__7 = (const lean_object*)&l_Lean_Grind_nodeDefUnexpander___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Grind_nodeDefUnexpander___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_nodeDefUnexpander(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_nodeDefUnexpander___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Grind_NodeDefUnexpander___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NodeDef"};
static const lean_object* l_Lean_Grind_NodeDefUnexpander___redArg___closed__0 = (const lean_object*)&l_Lean_Grind_NodeDefUnexpander___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Grind_NodeDefUnexpander___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_NodeDefUnexpander___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 91, 42, 70, 184, 75, 32, 170)}};
static const lean_object* l_Lean_Grind_NodeDefUnexpander___redArg___closed__1 = (const lean_object*)&l_Lean_Grind_NodeDefUnexpander___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Grind_NodeDefUnexpander___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_NodeDefUnexpander___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Grind_NodeDefUnexpander___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_NodeDefUnexpander(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_NodeDefUnexpander___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_NodeDef_toCtorIdx(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_node__def(lean_object* v_x_3_, lean_object* v_00_u03b1_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_box(0);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_node__def___boxed(lean_object* v_x_7_, lean_object* v_00_u03b1_8_, lean_object* v_a_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Grind_node__def(v_x_7_, v_00_u03b1_8_, v_a_9_);
lean_dec(v_a_9_);
lean_dec(v_x_7_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_nodeDefUnexpander___redArg(lean_object* v_stx_24_, lean_object* v_a_25_){
_start:
{
lean_object* v___x_26_; uint8_t v___x_27_; 
v___x_26_ = ((lean_object*)(l_Lean_Grind_nodeDefUnexpander___redArg___closed__4));
lean_inc(v_stx_24_);
v___x_27_ = l_Lean_Syntax_isOfKind(v_stx_24_, v___x_26_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; lean_object* v___x_29_; 
lean_dec(v_stx_24_);
v___x_28_ = lean_box(0);
v___x_29_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v_a_25_);
return v___x_29_;
}
else
{
lean_object* v___x_30_; lean_object* v___x_31_; uint8_t v___x_32_; 
v___x_30_ = lean_unsigned_to_nat(1u);
v___x_31_ = l_Lean_Syntax_getArg(v_stx_24_, v___x_30_);
lean_dec(v_stx_24_);
lean_inc(v___x_31_);
v___x_32_ = l_Lean_Syntax_matchesNull(v___x_31_, v___x_30_);
if (v___x_32_ == 0)
{
lean_object* v___x_33_; lean_object* v___x_34_; 
lean_dec(v___x_31_);
v___x_33_ = lean_box(0);
v___x_34_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
lean_ctor_set(v___x_34_, 1, v_a_25_);
return v___x_34_;
}
else
{
lean_object* v___x_35_; lean_object* v_id_36_; lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_35_ = lean_unsigned_to_nat(0u);
v_id_36_ = l_Lean_Syntax_getArg(v___x_31_, v___x_35_);
lean_dec(v___x_31_);
v___x_37_ = ((lean_object*)(l_Lean_Grind_nodeDefUnexpander___redArg___closed__6));
lean_inc(v_id_36_);
v___x_38_ = l_Lean_Syntax_isOfKind(v_id_36_, v___x_37_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; lean_object* v___x_40_; 
lean_dec(v_id_36_);
v___x_39_ = lean_box(0);
v___x_40_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
lean_ctor_set(v___x_40_, 1, v_a_25_);
return v___x_40_;
}
else
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_41_ = ((lean_object*)(l_Lean_Grind_nodeDefUnexpander___redArg___closed__7));
v___x_42_ = l_Lean_TSyntax_getNat(v_id_36_);
lean_dec(v_id_36_);
v___x_43_ = l_Nat_reprFast(v___x_42_);
v___x_44_ = lean_string_append(v___x_41_, v___x_43_);
lean_dec_ref(v___x_43_);
v___x_45_ = lean_box(0);
v___x_46_ = l_Lean_Name_str___override(v___x_45_, v___x_44_);
v___x_47_ = lean_mk_syntax_ident(v___x_46_);
v___x_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v_a_25_);
return v___x_48_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_nodeDefUnexpander(lean_object* v_stx_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_Grind_nodeDefUnexpander___redArg(v_stx_49_, v_a_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_nodeDefUnexpander___boxed(lean_object* v_stx_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Grind_nodeDefUnexpander(v_stx_53_, v_a_54_, v_a_55_);
lean_dec(v_a_54_);
return v_res_56_;
}
}
static lean_object* _init_l_Lean_Grind_NodeDefUnexpander___redArg___closed__2(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = ((lean_object*)(l_Lean_Grind_NodeDefUnexpander___redArg___closed__1));
v___x_62_ = lean_mk_syntax_ident(v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_NodeDefUnexpander___redArg(lean_object* v_a_63_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lean_obj_once(&l_Lean_Grind_NodeDefUnexpander___redArg___closed__2, &l_Lean_Grind_NodeDefUnexpander___redArg___closed__2_once, _init_l_Lean_Grind_NodeDefUnexpander___redArg___closed__2);
v___x_65_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v_a_63_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_NodeDefUnexpander(lean_object* v_x_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_Grind_NodeDefUnexpander___redArg(v_a_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_NodeDefUnexpander___boxed(lean_object* v_x_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_Grind_NodeDefUnexpander(v_x_70_, v_a_71_, v_a_72_);
lean_dec(v_a_71_);
lean_dec(v_x_70_);
return v_res_73_;
}
}
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_PP(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Grind_PP(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_PP(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Grind_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Grind_PP(builtin);
}
#ifdef __cplusplus
}
#endif

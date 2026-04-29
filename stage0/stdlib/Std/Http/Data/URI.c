// Lean compiler output
// Module: Std.Http.Data.URI
// Imports: public import Std.Http.Data.URI.Basic public import Std.Http.Data.URI.Parser
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
lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object*, lean_object*);
lean_object* l_Std_Http_URI_Parser_parseURI(lean_object*, lean_object*);
extern lean_object* l_Std_Http_instInhabitedURI_default;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Std_Http_instInhabitedRequestTarget_default;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_Http_URI_Parser_parsePath(lean_object*, uint8_t, uint8_t, lean_object*);
static const lean_string_object l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "expected end of input"};
static const lean_object* l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__0 = (const lean_object*)&l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__0_value)}};
static const lean_object* l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__1 = (const lean_object*)&l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_parse_x3f___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_RequestTarget_parse_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*9 + 0, .m_other = 9, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(253) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(256) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(128) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(100) << 1) | 1))}};
static const lean_object* l_Std_Http_RequestTarget_parse_x3f___closed__0 = (const lean_object*)&l_Std_Http_RequestTarget_parse_x3f___closed__0_value;
static const lean_closure_object l_Std_Http_RequestTarget_parse_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_RequestTarget_parse_x3f___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_RequestTarget_parse_x3f___closed__0_value)} };
static const lean_object* l_Std_Http_RequestTarget_parse_x3f___closed__1 = (const lean_object*)&l_Std_Http_RequestTarget_parse_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_parse_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_parse_x3f___boxed(lean_object*);
static const lean_string_object l_Std_Http_RequestTarget_parse_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Std.Http.Data.URI"};
static const lean_object* l_Std_Http_RequestTarget_parse_x21___closed__0 = (const lean_object*)&l_Std_Http_RequestTarget_parse_x21___closed__0_value;
static const lean_string_object l_Std_Http_RequestTarget_parse_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Std.Http.RequestTarget.parse!"};
static const lean_object* l_Std_Http_RequestTarget_parse_x21___closed__1 = (const lean_object*)&l_Std_Http_RequestTarget_parse_x21___closed__1_value;
static const lean_string_object l_Std_Http_RequestTarget_parse_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid request target"};
static const lean_object* l_Std_Http_RequestTarget_parse_x21___closed__2 = (const lean_object*)&l_Std_Http_RequestTarget_parse_x21___closed__2_value;
static lean_once_cell_t l_Std_Http_RequestTarget_parse_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_RequestTarget_parse_x21___closed__3;
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_parse_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_parse_x21___boxed(lean_object*);
static const lean_string_object l_Std_Http_RequestTarget_originForm_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Std.Http.RequestTarget.originForm!"};
static const lean_object* l_Std_Http_RequestTarget_originForm_x21___closed__0 = (const lean_object*)&l_Std_Http_RequestTarget_originForm_x21___closed__0_value;
static const lean_string_object l_Std_Http_RequestTarget_originForm_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "invalid origin-form request target: "};
static const lean_object* l_Std_Http_RequestTarget_originForm_x21___closed__1 = (const lean_object*)&l_Std_Http_RequestTarget_originForm_x21___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_parse_x3f___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_parse_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_parse_x3f___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_RequestTarget_parse_x3f___closed__0_value)} };
static const lean_object* l_Std_Http_URI_parse_x3f___closed__0 = (const lean_object*)&l_Std_Http_URI_parse_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_parse_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_parse_x3f___boxed(lean_object*);
static const lean_string_object l_Std_Http_URI_parse_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Http.URI.parse!"};
static const lean_object* l_Std_Http_URI_parse_x21___closed__0 = (const lean_object*)&l_Std_Http_URI_parse_x21___closed__0_value;
static const lean_string_object l_Std_Http_URI_parse_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "invalid URI"};
static const lean_object* l_Std_Http_URI_parse_x21___closed__1 = (const lean_object*)&l_Std_Http_URI_parse_x21___closed__1_value;
static lean_once_cell_t l_Std_Http_URI_parse_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_parse_x21___closed__2;
LEAN_EXPORT lean_object* l_Std_Http_URI_parse_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_parse_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parse_x3f___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parse_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_Path_parse_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_Path_parse_x3f___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_RequestTarget_parse_x3f___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Std_Http_URI_Path_parse_x3f___closed__0 = (const lean_object*)&l_Std_Http_URI_Path_parse_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parse_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parse_x3f___boxed(lean_object*);
static const lean_array_object l_Std_Http_URI_Path_parseOrRoot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_URI_Path_parseOrRoot___closed__0 = (const lean_object*)&l_Std_Http_URI_Path_parseOrRoot___closed__0_value;
static const lean_ctor_object l_Std_Http_URI_Path_parseOrRoot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_URI_Path_parseOrRoot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Http_URI_Path_parseOrRoot___closed__1 = (const lean_object*)&l_Std_Http_URI_Path_parseOrRoot___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parseOrRoot(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parseOrRoot___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_parse_x3f___lam__0(lean_object* v___x_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = l_Std_Http_URI_Parser_parseRequestTarget(v___x_4_, v___y_5_);
if (lean_obj_tag(v___x_6_) == 0)
{
lean_object* v_pos_7_; lean_object* v_array_8_; lean_object* v_idx_9_; lean_object* v___x_10_; uint8_t v___x_11_; 
v_pos_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_pos_7_);
v_array_8_ = lean_ctor_get(v_pos_7_, 0);
v_idx_9_ = lean_ctor_get(v_pos_7_, 1);
v___x_10_ = lean_byte_array_size(v_array_8_);
v___x_11_ = lean_nat_dec_lt(v_idx_9_, v___x_10_);
if (v___x_11_ == 0)
{
lean_dec(v_pos_7_);
return v___x_6_;
}
else
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_6_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; lean_object* v_unused_21_; 
v_unused_20_ = lean_ctor_get(v___x_6_, 1);
lean_dec(v_unused_20_);
v_unused_21_ = lean_ctor_get(v___x_6_, 0);
lean_dec(v_unused_21_);
v___x_13_ = v___x_6_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_6_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
v___x_15_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__1));
if (v_isShared_14_ == 0)
{
lean_ctor_set_tag(v___x_13_, 1);
lean_ctor_set(v___x_13_, 1, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v_pos_7_);
lean_ctor_set(v_reuseFailAlloc_18_, 1, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
}
else
{
return v___x_6_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_parse_x3f(lean_object* v_string_32_){
_start:
{
lean_object* v___f_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___f_33_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x3f___closed__1));
v___x_34_ = lean_string_to_utf8(v_string_32_);
v___x_35_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_33_, v___x_34_);
if (lean_obj_tag(v___x_35_) == 0)
{
lean_object* v___x_36_; 
lean_dec_ref(v___x_35_);
v___x_36_ = lean_box(0);
return v___x_36_;
}
else
{
lean_object* v_a_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_44_; 
v_a_37_ = lean_ctor_get(v___x_35_, 0);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_44_ == 0)
{
v___x_39_ = v___x_35_;
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_a_37_);
lean_dec(v___x_35_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_42_; 
if (v_isShared_40_ == 0)
{
v___x_42_ = v___x_39_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v_a_37_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_parse_x3f___boxed(lean_object* v_string_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Std_Http_RequestTarget_parse_x3f(v_string_45_);
lean_dec_ref(v_string_45_);
return v_res_46_;
}
}
static lean_object* _init_l_Std_Http_RequestTarget_parse_x21___closed__3(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_50_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x21___closed__2));
v___x_51_ = lean_unsigned_to_nat(12u);
v___x_52_ = lean_unsigned_to_nat(45u);
v___x_53_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x21___closed__1));
v___x_54_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x21___closed__0));
v___x_55_ = l_mkPanicMessageWithDecl(v___x_54_, v___x_53_, v___x_52_, v___x_51_, v___x_50_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_parse_x21(lean_object* v_string_56_){
_start:
{
lean_object* v___f_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___f_57_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x3f___closed__1));
v___x_58_ = lean_string_to_utf8(v_string_56_);
v___x_59_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_57_, v___x_58_);
if (lean_obj_tag(v___x_59_) == 0)
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
lean_dec_ref(v___x_59_);
v___x_60_ = l_Std_Http_instInhabitedRequestTarget_default;
v___x_61_ = lean_obj_once(&l_Std_Http_RequestTarget_parse_x21___closed__3, &l_Std_Http_RequestTarget_parse_x21___closed__3_once, _init_l_Std_Http_RequestTarget_parse_x21___closed__3);
v___x_62_ = l_panic___redArg(v___x_60_, v___x_61_);
return v___x_62_;
}
else
{
lean_object* v_a_63_; 
v_a_63_ = lean_ctor_get(v___x_59_, 0);
lean_inc(v_a_63_);
lean_dec_ref(v___x_59_);
return v_a_63_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_parse_x21___boxed(lean_object* v_string_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Std_Http_RequestTarget_parse_x21(v_string_64_);
lean_dec_ref(v_string_64_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_x21(lean_object* v_path_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___f_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_69_ = l_Std_Http_instInhabitedRequestTarget_default;
v___f_79_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x3f___closed__1));
v___x_80_ = lean_string_to_utf8(v_path_68_);
v___x_81_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_79_, v___x_80_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_dec_ref(v___x_81_);
goto v___jp_70_;
}
else
{
lean_object* v_a_82_; 
v_a_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_a_82_);
lean_dec_ref(v___x_81_);
if (lean_obj_tag(v_a_82_) == 0)
{
return v_a_82_;
}
else
{
lean_dec(v_a_82_);
goto v___jp_70_;
}
}
v___jp_70_:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_71_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x21___closed__0));
v___x_72_ = ((lean_object*)(l_Std_Http_RequestTarget_originForm_x21___closed__0));
v___x_73_ = lean_unsigned_to_nat(56u);
v___x_74_ = lean_unsigned_to_nat(9u);
v___x_75_ = ((lean_object*)(l_Std_Http_RequestTarget_originForm_x21___closed__1));
v___x_76_ = lean_string_append(v___x_75_, v_path_68_);
v___x_77_ = l_mkPanicMessageWithDecl(v___x_71_, v___x_72_, v___x_73_, v___x_74_, v___x_76_);
lean_dec_ref(v___x_76_);
v___x_78_ = l_panic___redArg(v___x_69_, v___x_77_);
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_x21___boxed(lean_object* v_path_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Std_Http_RequestTarget_originForm_x21(v_path_83_);
lean_dec_ref(v_path_83_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_parse_x3f___lam__0(lean_object* v___x_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Std_Http_URI_Parser_parseURI(v___x_85_, v___y_86_);
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v_pos_88_; lean_object* v_array_89_; lean_object* v_idx_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v_pos_88_ = lean_ctor_get(v___x_87_, 0);
lean_inc(v_pos_88_);
v_array_89_ = lean_ctor_get(v_pos_88_, 0);
v_idx_90_ = lean_ctor_get(v_pos_88_, 1);
v___x_91_ = lean_byte_array_size(v_array_89_);
v___x_92_ = lean_nat_dec_lt(v_idx_90_, v___x_91_);
if (v___x_92_ == 0)
{
lean_dec(v_pos_88_);
return v___x_87_;
}
else
{
lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_100_; 
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; lean_object* v_unused_102_; 
v_unused_101_ = lean_ctor_get(v___x_87_, 1);
lean_dec(v_unused_101_);
v_unused_102_ = lean_ctor_get(v___x_87_, 0);
lean_dec(v_unused_102_);
v___x_94_ = v___x_87_;
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
else
{
lean_dec(v___x_87_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_96_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__1));
if (v_isShared_95_ == 0)
{
lean_ctor_set_tag(v___x_94_, 1);
lean_ctor_set(v___x_94_, 1, v___x_96_);
v___x_98_ = v___x_94_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_pos_88_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
else
{
return v___x_87_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_parse_x3f(lean_object* v_string_105_){
_start:
{
lean_object* v___f_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___f_106_ = ((lean_object*)(l_Std_Http_URI_parse_x3f___closed__0));
v___x_107_ = lean_string_to_utf8(v_string_105_);
v___x_108_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_106_, v___x_107_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v___x_109_; 
lean_dec_ref(v___x_108_);
v___x_109_ = lean_box(0);
return v___x_109_;
}
else
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
v_a_110_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_108_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_108_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_parse_x3f___boxed(lean_object* v_string_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Std_Http_URI_parse_x3f(v_string_118_);
lean_dec_ref(v_string_118_);
return v_res_119_;
}
}
static lean_object* _init_l_Std_Http_URI_parse_x21___closed__2(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_122_ = ((lean_object*)(l_Std_Http_URI_parse_x21___closed__1));
v___x_123_ = lean_unsigned_to_nat(12u);
v___x_124_ = lean_unsigned_to_nat(77u);
v___x_125_ = ((lean_object*)(l_Std_Http_URI_parse_x21___closed__0));
v___x_126_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x21___closed__0));
v___x_127_ = l_mkPanicMessageWithDecl(v___x_126_, v___x_125_, v___x_124_, v___x_123_, v___x_122_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_parse_x21(lean_object* v_string_128_){
_start:
{
lean_object* v___f_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___f_129_ = ((lean_object*)(l_Std_Http_URI_parse_x3f___closed__0));
v___x_130_ = lean_string_to_utf8(v_string_128_);
v___x_131_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_129_, v___x_130_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
lean_dec_ref(v___x_131_);
v___x_132_ = l_Std_Http_instInhabitedURI_default;
v___x_133_ = lean_obj_once(&l_Std_Http_URI_parse_x21___closed__2, &l_Std_Http_URI_parse_x21___closed__2_once, _init_l_Std_Http_URI_parse_x21___closed__2);
v___x_134_ = l_panic___redArg(v___x_132_, v___x_133_);
return v___x_134_;
}
else
{
lean_object* v_a_135_; 
v_a_135_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_a_135_);
lean_dec_ref(v___x_131_);
return v_a_135_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_parse_x21___boxed(lean_object* v_string_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Std_Http_URI_parse_x21(v_string_136_);
lean_dec_ref(v_string_136_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parse_x3f___lam__0(lean_object* v___x_138_, uint8_t v___x_139_, lean_object* v___y_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Std_Http_URI_Parser_parsePath(v___x_138_, v___x_139_, v___x_139_, v___y_140_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v_pos_142_; lean_object* v_array_143_; lean_object* v_idx_144_; lean_object* v___x_145_; uint8_t v___x_146_; 
v_pos_142_ = lean_ctor_get(v___x_141_, 0);
lean_inc(v_pos_142_);
v_array_143_ = lean_ctor_get(v_pos_142_, 0);
v_idx_144_ = lean_ctor_get(v_pos_142_, 1);
v___x_145_ = lean_byte_array_size(v_array_143_);
v___x_146_ = lean_nat_dec_lt(v_idx_144_, v___x_145_);
if (v___x_146_ == 0)
{
lean_dec(v_pos_142_);
return v___x_141_;
}
else
{
lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_154_; 
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_154_ == 0)
{
lean_object* v_unused_155_; lean_object* v_unused_156_; 
v_unused_155_ = lean_ctor_get(v___x_141_, 1);
lean_dec(v_unused_155_);
v_unused_156_ = lean_ctor_get(v___x_141_, 0);
lean_dec(v_unused_156_);
v___x_148_ = v___x_141_;
v_isShared_149_ = v_isSharedCheck_154_;
goto v_resetjp_147_;
}
else
{
lean_dec(v___x_141_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_154_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_150_; lean_object* v___x_152_; 
v___x_150_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__1));
if (v_isShared_149_ == 0)
{
lean_ctor_set_tag(v___x_148_, 1);
lean_ctor_set(v___x_148_, 1, v___x_150_);
v___x_152_ = v___x_148_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_pos_142_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v___x_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
else
{
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parse_x3f___lam__0___boxed(lean_object* v___x_157_, lean_object* v___x_158_, lean_object* v___y_159_){
_start:
{
uint8_t v___x_274__boxed_160_; lean_object* v_res_161_; 
v___x_274__boxed_160_ = lean_unbox(v___x_158_);
v_res_161_ = l_Std_Http_URI_Path_parse_x3f___lam__0(v___x_157_, v___x_274__boxed_160_, v___y_159_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parse_x3f(lean_object* v_s_166_){
_start:
{
lean_object* v___f_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___f_167_ = ((lean_object*)(l_Std_Http_URI_Path_parse_x3f___closed__0));
v___x_168_ = lean_string_to_utf8(v_s_166_);
v___x_169_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_167_, v___x_168_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v___x_170_; 
lean_dec_ref(v___x_169_);
v___x_170_ = lean_box(0);
return v___x_170_;
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
v_a_171_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_169_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_169_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parse_x3f___boxed(lean_object* v_s_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Std_Http_URI_Path_parse_x3f(v_s_179_);
lean_dec_ref(v_s_179_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parseOrRoot(lean_object* v_s_186_){
_start:
{
lean_object* v___f_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___f_187_ = ((lean_object*)(l_Std_Http_URI_Path_parse_x3f___closed__0));
v___x_188_ = lean_string_to_utf8(v_s_186_);
v___x_189_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_187_, v___x_188_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v___x_190_; 
lean_dec_ref(v___x_189_);
v___x_190_ = ((lean_object*)(l_Std_Http_URI_Path_parseOrRoot___closed__1));
return v___x_190_;
}
else
{
lean_object* v_a_191_; 
v_a_191_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_a_191_);
lean_dec_ref(v___x_189_);
return v_a_191_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parseOrRoot___boxed(lean_object* v_s_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Std_Http_URI_Path_parseOrRoot(v_s_192_);
lean_dec_ref(v_s_192_);
return v_res_193_;
}
}
lean_object* runtime_initialize_Std_Http_Data_URI_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_URI_Parser(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_URI(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Http_Data_URI_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_URI_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Data_URI(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Http_Data_URI_Basic(uint8_t builtin);
lean_object* initialize_Std_Http_Data_URI_Parser(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Data_URI(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Http_Data_URI_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_URI_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_URI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Data_URI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Data_URI(builtin);
}
#ifdef __cplusplus
}
#endif

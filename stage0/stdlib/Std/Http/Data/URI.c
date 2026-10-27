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
lean_object* l_Std_Http_URI_Parser_parseURI(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object*, lean_object*);
extern lean_object* l_Std_Http_instInhabitedURI_default;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
uint16_t l_Std_Http_URI_Scheme_defaultPort(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Std_Http_instInhabitedRequestTarget_default;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object*, lean_object*);
lean_object* l_Std_Http_URI_Query_insert(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Http_URI_Query_empty;
lean_object* l_Std_Http_URI_Parser_parsePath(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Std_Http_URI_Parser_parseURIReference(lean_object*, lean_object*);
extern lean_object* l_Std_Http_instInhabitedURIReference_default;
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
static const lean_string_object l_Std_Http_RequestTarget_parse_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Std.Http.Data.URI"};
static const lean_object* l_Std_Http_RequestTarget_parse_x21___closed__0 = (const lean_object*)&l_Std_Http_RequestTarget_parse_x21___closed__0_value;
static const lean_string_object l_Std_Http_RequestTarget_parse_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Std.Http.RequestTarget.parse!"};
static const lean_object* l_Std_Http_RequestTarget_parse_x21___closed__1 = (const lean_object*)&l_Std_Http_RequestTarget_parse_x21___closed__1_value;
static const lean_string_object l_Std_Http_RequestTarget_parse_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid request target"};
static const lean_object* l_Std_Http_RequestTarget_parse_x21___closed__2 = (const lean_object*)&l_Std_Http_RequestTarget_parse_x21___closed__2_value;
static lean_once_cell_t l_Std_Http_RequestTarget_parse_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_RequestTarget_parse_x21___closed__3;
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_parse_x21(lean_object*);
static const lean_string_object l_Std_Http_RequestTarget_originForm_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Std.Http.RequestTarget.originForm!"};
static const lean_object* l_Std_Http_RequestTarget_originForm_x21___closed__0 = (const lean_object*)&l_Std_Http_RequestTarget_originForm_x21___closed__0_value;
static const lean_string_object l_Std_Http_RequestTarget_originForm_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "invalid origin-form request target: "};
static const lean_object* l_Std_Http_RequestTarget_originForm_x21___closed__1 = (const lean_object*)&l_Std_Http_RequestTarget_originForm_x21___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_x21(lean_object*);
static const lean_array_object l_Std_Http_RequestTarget_pathOrRoot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_RequestTarget_pathOrRoot___closed__0 = (const lean_object*)&l_Std_Http_RequestTarget_pathOrRoot___closed__0_value;
static const lean_ctor_object l_Std_Http_RequestTarget_pathOrRoot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_RequestTarget_pathOrRoot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Http_RequestTarget_pathOrRoot___closed__1 = (const lean_object*)&l_Std_Http_RequestTarget_pathOrRoot___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_pathOrRoot(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_pathOrRoot___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_setQueryParam(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URIReference_parse_x3f___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URIReference_parse_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URIReference_parse_x3f___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_RequestTarget_parse_x3f___closed__0_value)} };
static const lean_object* l_Std_Http_URIReference_parse_x3f___closed__0 = (const lean_object*)&l_Std_Http_URIReference_parse_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URIReference_parse_x3f(lean_object*);
static const lean_string_object l_Std_Http_URIReference_parse_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Std.Http.URIReference.parse!"};
static const lean_object* l_Std_Http_URIReference_parse_x21___closed__0 = (const lean_object*)&l_Std_Http_URIReference_parse_x21___closed__0_value;
static const lean_string_object l_Std_Http_URIReference_parse_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "invalid URI reference"};
static const lean_object* l_Std_Http_URIReference_parse_x21___closed__1 = (const lean_object*)&l_Std_Http_URIReference_parse_x21___closed__1_value;
static lean_once_cell_t l_Std_Http_URIReference_parse_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URIReference_parse_x21___closed__2;
LEAN_EXPORT lean_object* l_Std_Http_URIReference_parse_x21(lean_object*);
LEAN_EXPORT uint16_t l_Std_Http_URI_port(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_port___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_host_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_originTarget(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_originTarget___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_parse_x3f___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_parse_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_parse_x3f___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_RequestTarget_parse_x3f___closed__0_value)} };
static const lean_object* l_Std_Http_URI_parse_x3f___closed__0 = (const lean_object*)&l_Std_Http_URI_parse_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_parse_x3f(lean_object*);
static const lean_string_object l_Std_Http_URI_parse_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Http.URI.parse!"};
static const lean_object* l_Std_Http_URI_parse_x21___closed__0 = (const lean_object*)&l_Std_Http_URI_parse_x21___closed__0_value;
static const lean_string_object l_Std_Http_URI_parse_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "invalid URI"};
static const lean_object* l_Std_Http_URI_parse_x21___closed__1 = (const lean_object*)&l_Std_Http_URI_parse_x21___closed__1_value;
static lean_once_cell_t l_Std_Http_URI_parse_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_parse_x21___closed__2;
LEAN_EXPORT lean_object* l_Std_Http_URI_parse_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parse_x3f___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parse_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URI_Path_parse_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URI_Path_parse_x3f___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_RequestTarget_parse_x3f___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Std_Http_URI_Path_parse_x3f___closed__0 = (const lean_object*)&l_Std_Http_URI_Path_parse_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parse_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parseOrRoot(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_parse_x3f___lam__0(lean_object* v___x_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = l_Std_Http_URI_Parser_parseRequestTarget(v___x_4_, v___y_5_);
if (lean_obj_tag(v___x_6_) == 0)
{
lean_object* v_pos_7_; lean_object* v_array_8_; lean_object* v_idx_9_; lean_object* v___x_10_; uint8_t v___x_11_; 
v_pos_7_ = lean_ctor_get(v___x_6_, 0);
v_array_8_ = lean_ctor_get(v_pos_7_, 0);
v_idx_9_ = lean_ctor_get(v_pos_7_, 1);
v___x_10_ = lean_byte_array_size(v_array_8_);
v___x_11_ = lean_nat_dec_lt(v_idx_9_, v___x_10_);
if (v___x_11_ == 0)
{
return v___x_6_;
}
else
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
lean_inc(v_pos_7_);
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
lean_dec_ref_known(v___x_35_, 1);
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
static lean_object* _init_l_Std_Http_RequestTarget_parse_x21___closed__3(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_48_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x21___closed__2));
v___x_49_ = lean_unsigned_to_nat(12u);
v___x_50_ = lean_unsigned_to_nat(45u);
v___x_51_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x21___closed__1));
v___x_52_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x21___closed__0));
v___x_53_ = l_mkPanicMessageWithDecl(v___x_52_, v___x_51_, v___x_50_, v___x_49_, v___x_48_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_parse_x21(lean_object* v_string_54_){
_start:
{
lean_object* v___f_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___f_55_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x3f___closed__1));
v___x_56_ = lean_string_to_utf8(v_string_54_);
v___x_57_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_55_, v___x_56_);
if (lean_obj_tag(v___x_57_) == 0)
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec_ref_known(v___x_57_, 1);
v___x_58_ = l_Std_Http_instInhabitedRequestTarget_default;
v___x_59_ = lean_obj_once(&l_Std_Http_RequestTarget_parse_x21___closed__3, &l_Std_Http_RequestTarget_parse_x21___closed__3_once, _init_l_Std_Http_RequestTarget_parse_x21___closed__3);
v___x_60_ = l_panic___redArg(v___x_58_, v___x_59_);
return v___x_60_;
}
else
{
lean_object* v_a_61_; 
v_a_61_ = lean_ctor_get(v___x_57_, 0);
lean_inc(v_a_61_);
lean_dec_ref_known(v___x_57_, 1);
return v_a_61_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_x21(lean_object* v_path_64_){
_start:
{
lean_object* v___x_65_; lean_object* v___f_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_65_ = l_Std_Http_instInhabitedRequestTarget_default;
v___f_75_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x3f___closed__1));
lean_inc_ref(v_path_64_);
v___x_76_ = lean_string_to_utf8(v_path_64_);
v___x_77_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_75_, v___x_76_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_dec_ref_known(v___x_77_, 1);
goto v___jp_66_;
}
else
{
lean_object* v_a_78_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc(v_a_78_);
lean_dec_ref_known(v___x_77_, 1);
if (lean_obj_tag(v_a_78_) == 0)
{
lean_dec_ref(v_path_64_);
return v_a_78_;
}
else
{
lean_dec(v_a_78_);
goto v___jp_66_;
}
}
v___jp_66_:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_67_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x21___closed__0));
v___x_68_ = ((lean_object*)(l_Std_Http_RequestTarget_originForm_x21___closed__0));
v___x_69_ = lean_unsigned_to_nat(55u);
v___x_70_ = lean_unsigned_to_nat(9u);
v___x_71_ = ((lean_object*)(l_Std_Http_RequestTarget_originForm_x21___closed__1));
v___x_72_ = lean_string_append(v___x_71_, v_path_64_);
lean_dec_ref(v_path_64_);
v___x_73_ = l_mkPanicMessageWithDecl(v___x_67_, v___x_68_, v___x_69_, v___x_70_, v___x_72_);
lean_dec_ref(v___x_72_);
v___x_74_ = l_panic___redArg(v___x_65_, v___x_73_);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_pathOrRoot(lean_object* v_x_84_){
_start:
{
switch(lean_obj_tag(v_x_84_))
{
case 0:
{
lean_object* v_path_85_; 
v_path_85_ = lean_ctor_get(v_x_84_, 0);
lean_inc_ref(v_path_85_);
return v_path_85_;
}
case 1:
{
lean_object* v_uri_86_; lean_object* v_path_87_; 
v_uri_86_ = lean_ctor_get(v_x_84_, 0);
v_path_87_ = lean_ctor_get(v_uri_86_, 2);
lean_inc_ref(v_path_87_);
return v_path_87_;
}
default: 
{
lean_object* v___x_88_; 
v___x_88_ = ((lean_object*)(l_Std_Http_RequestTarget_pathOrRoot___closed__1));
return v___x_88_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_pathOrRoot___boxed(lean_object* v_x_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Std_Http_RequestTarget_pathOrRoot(v_x_89_);
lean_dec(v_x_89_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_setQueryParam(lean_object* v_target_91_, lean_object* v_key_92_, lean_object* v_value_93_){
_start:
{
switch(lean_obj_tag(v_target_91_))
{
case 0:
{
lean_object* v_path_94_; lean_object* v_query_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_108_; 
v_path_94_ = lean_ctor_get(v_target_91_, 0);
v_query_95_ = lean_ctor_get(v_target_91_, 1);
v_isSharedCheck_108_ = !lean_is_exclusive(v_target_91_);
if (v_isSharedCheck_108_ == 0)
{
v___x_97_ = v_target_91_;
v_isShared_98_ = v_isSharedCheck_108_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_query_95_);
lean_inc(v_path_94_);
lean_dec(v_target_91_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_108_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___y_100_; 
if (lean_obj_tag(v_query_95_) == 0)
{
lean_object* v___x_106_; 
v___x_106_ = l_Std_Http_URI_Query_empty;
v___y_100_ = v___x_106_;
goto v___jp_99_;
}
else
{
lean_object* v_val_107_; 
v_val_107_ = lean_ctor_get(v_query_95_, 0);
lean_inc(v_val_107_);
lean_dec_ref_known(v_query_95_, 1);
v___y_100_ = v_val_107_;
goto v___jp_99_;
}
v___jp_99_:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_104_; 
v___x_101_ = l_Std_Http_URI_Query_insert(v___y_100_, v_key_92_, v_value_93_);
v___x_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 1, v___x_102_);
v___x_104_ = v___x_97_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_path_94_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v___x_102_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
}
case 1:
{
lean_object* v_uri_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_134_; 
v_uri_109_ = lean_ctor_get(v_target_91_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v_target_91_);
if (v_isSharedCheck_134_ == 0)
{
v___x_111_ = v_target_91_;
v_isShared_112_ = v_isSharedCheck_134_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_uri_109_);
lean_dec(v_target_91_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_134_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v_scheme_113_; lean_object* v_authority_114_; lean_object* v_path_115_; lean_object* v_query_116_; lean_object* v_fragment_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_133_; 
v_scheme_113_ = lean_ctor_get(v_uri_109_, 0);
v_authority_114_ = lean_ctor_get(v_uri_109_, 1);
v_path_115_ = lean_ctor_get(v_uri_109_, 2);
v_query_116_ = lean_ctor_get(v_uri_109_, 3);
v_fragment_117_ = lean_ctor_get(v_uri_109_, 4);
v_isSharedCheck_133_ = !lean_is_exclusive(v_uri_109_);
if (v_isSharedCheck_133_ == 0)
{
v___x_119_ = v_uri_109_;
v_isShared_120_ = v_isSharedCheck_133_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_fragment_117_);
lean_inc(v_query_116_);
lean_inc(v_path_115_);
lean_inc(v_authority_114_);
lean_inc(v_scheme_113_);
lean_dec(v_uri_109_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_133_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___y_122_; 
if (lean_obj_tag(v_query_116_) == 0)
{
lean_object* v___x_131_; 
v___x_131_ = l_Std_Http_URI_Query_empty;
v___y_122_ = v___x_131_;
goto v___jp_121_;
}
else
{
lean_object* v_val_132_; 
v_val_132_ = lean_ctor_get(v_query_116_, 0);
lean_inc(v_val_132_);
lean_dec_ref_known(v_query_116_, 1);
v___y_122_ = v_val_132_;
goto v___jp_121_;
}
v___jp_121_:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_126_; 
v___x_123_ = l_Std_Http_URI_Query_insert(v___y_122_, v_key_92_, v_value_93_);
v___x_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 3, v___x_124_);
v___x_126_ = v___x_119_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_scheme_113_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v_authority_114_);
lean_ctor_set(v_reuseFailAlloc_130_, 2, v_path_115_);
lean_ctor_set(v_reuseFailAlloc_130_, 3, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_130_, 4, v_fragment_117_);
v___x_126_ = v_reuseFailAlloc_130_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v___x_128_; 
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_126_);
v___x_128_ = v___x_111_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_126_);
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
}
default: 
{
lean_dec_ref(v_value_93_);
lean_dec_ref(v_key_92_);
return v_target_91_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_parse_x3f___lam__0(lean_object* v___x_135_, lean_object* v___y_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Std_Http_URI_Parser_parseURIReference(v___x_135_, v___y_136_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_pos_138_; lean_object* v_array_139_; lean_object* v_idx_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v_pos_138_ = lean_ctor_get(v___x_137_, 0);
v_array_139_ = lean_ctor_get(v_pos_138_, 0);
v_idx_140_ = lean_ctor_get(v_pos_138_, 1);
v___x_141_ = lean_byte_array_size(v_array_139_);
v___x_142_ = lean_nat_dec_lt(v_idx_140_, v___x_141_);
if (v___x_142_ == 0)
{
return v___x_137_;
}
else
{
lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_150_; 
lean_inc(v_pos_138_);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_150_ == 0)
{
lean_object* v_unused_151_; lean_object* v_unused_152_; 
v_unused_151_ = lean_ctor_get(v___x_137_, 1);
lean_dec(v_unused_151_);
v_unused_152_ = lean_ctor_get(v___x_137_, 0);
lean_dec(v_unused_152_);
v___x_144_ = v___x_137_;
v_isShared_145_ = v_isSharedCheck_150_;
goto v_resetjp_143_;
}
else
{
lean_dec(v___x_137_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_150_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_146_; lean_object* v___x_148_; 
v___x_146_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__1));
if (v_isShared_145_ == 0)
{
lean_ctor_set_tag(v___x_144_, 1);
lean_ctor_set(v___x_144_, 1, v___x_146_);
v___x_148_ = v___x_144_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_pos_138_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v___x_146_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
else
{
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_parse_x3f(lean_object* v_string_155_){
_start:
{
lean_object* v___f_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___f_156_ = ((lean_object*)(l_Std_Http_URIReference_parse_x3f___closed__0));
v___x_157_ = lean_string_to_utf8(v_string_155_);
v___x_158_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_156_, v___x_157_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v___x_159_; 
lean_dec_ref_known(v___x_158_, 1);
v___x_159_ = lean_box(0);
return v___x_159_;
}
else
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
v_a_160_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_158_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_158_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_160_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
}
static lean_object* _init_l_Std_Http_URIReference_parse_x21___closed__2(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_170_ = ((lean_object*)(l_Std_Http_URIReference_parse_x21___closed__1));
v___x_171_ = lean_unsigned_to_nat(12u);
v___x_172_ = lean_unsigned_to_nat(106u);
v___x_173_ = ((lean_object*)(l_Std_Http_URIReference_parse_x21___closed__0));
v___x_174_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x21___closed__0));
v___x_175_ = l_mkPanicMessageWithDecl(v___x_174_, v___x_173_, v___x_172_, v___x_171_, v___x_170_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_parse_x21(lean_object* v_string_176_){
_start:
{
lean_object* v___f_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___f_177_ = ((lean_object*)(l_Std_Http_URIReference_parse_x3f___closed__0));
v___x_178_ = lean_string_to_utf8(v_string_176_);
v___x_179_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_177_, v___x_178_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec_ref_known(v___x_179_, 1);
v___x_180_ = l_Std_Http_instInhabitedURIReference_default;
v___x_181_ = lean_obj_once(&l_Std_Http_URIReference_parse_x21___closed__2, &l_Std_Http_URIReference_parse_x21___closed__2_once, _init_l_Std_Http_URIReference_parse_x21___closed__2);
v___x_182_ = l_panic___redArg(v___x_180_, v___x_181_);
return v___x_182_;
}
else
{
lean_object* v_a_183_; 
v_a_183_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_183_);
lean_dec_ref_known(v___x_179_, 1);
return v_a_183_;
}
}
}
LEAN_EXPORT uint16_t l_Std_Http_URI_port(lean_object* v_uri_184_){
_start:
{
lean_object* v_authority_185_; 
v_authority_185_ = lean_ctor_get(v_uri_184_, 1);
if (lean_obj_tag(v_authority_185_) == 0)
{
lean_object* v_scheme_186_; uint16_t v___x_187_; 
v_scheme_186_ = lean_ctor_get(v_uri_184_, 0);
v___x_187_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_186_);
return v___x_187_;
}
else
{
lean_object* v_val_188_; lean_object* v_port_189_; 
v_val_188_ = lean_ctor_get(v_authority_185_, 0);
v_port_189_ = lean_ctor_get(v_val_188_, 2);
if (lean_obj_tag(v_port_189_) == 2)
{
uint16_t v_port_190_; 
v_port_190_ = lean_ctor_get_uint16(v_port_189_, 0);
return v_port_190_;
}
else
{
lean_object* v_scheme_191_; uint16_t v___x_192_; 
v_scheme_191_ = lean_ctor_get(v_uri_184_, 0);
v___x_192_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_191_);
return v___x_192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_port___boxed(lean_object* v_uri_193_){
_start:
{
uint16_t v_res_194_; lean_object* v_r_195_; 
v_res_194_ = l_Std_Http_URI_port(v_uri_193_);
lean_dec_ref(v_uri_193_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_host_x3f(lean_object* v_uri_196_){
_start:
{
lean_object* v_authority_197_; 
v_authority_197_ = lean_ctor_get(v_uri_196_, 1);
lean_inc(v_authority_197_);
lean_dec_ref(v_uri_196_);
if (lean_obj_tag(v_authority_197_) == 0)
{
lean_object* v___x_198_; 
v___x_198_ = lean_box(0);
return v___x_198_;
}
else
{
lean_object* v_val_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_207_; 
v_val_199_ = lean_ctor_get(v_authority_197_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v_authority_197_);
if (v_isSharedCheck_207_ == 0)
{
v___x_201_ = v_authority_197_;
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_val_199_);
lean_dec(v_authority_197_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v_host_203_; lean_object* v___x_205_; 
v_host_203_ = lean_ctor_get(v_val_199_, 1);
lean_inc_ref(v_host_203_);
lean_dec(v_val_199_);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v_host_203_);
v___x_205_ = v___x_201_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_host_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_originTarget(lean_object* v_uri_208_){
_start:
{
lean_object* v_path_209_; lean_object* v_query_210_; lean_object* v___x_211_; 
v_path_209_ = lean_ctor_get(v_uri_208_, 2);
v_query_210_ = lean_ctor_get(v_uri_208_, 3);
lean_inc(v_query_210_);
lean_inc_ref(v_path_209_);
v___x_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_211_, 0, v_path_209_);
lean_ctor_set(v___x_211_, 1, v_query_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_originTarget___boxed(lean_object* v_uri_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Std_Http_URI_originTarget(v_uri_212_);
lean_dec_ref(v_uri_212_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_parse_x3f___lam__0(lean_object* v___x_214_, lean_object* v___y_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Std_Http_URI_Parser_parseURI(v___x_214_, v___y_215_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_pos_217_; lean_object* v_array_218_; lean_object* v_idx_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v_pos_217_ = lean_ctor_get(v___x_216_, 0);
v_array_218_ = lean_ctor_get(v_pos_217_, 0);
v_idx_219_ = lean_ctor_get(v_pos_217_, 1);
v___x_220_ = lean_byte_array_size(v_array_218_);
v___x_221_ = lean_nat_dec_lt(v_idx_219_, v___x_220_);
if (v___x_221_ == 0)
{
return v___x_216_;
}
else
{
lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_229_; 
lean_inc(v_pos_217_);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_229_ == 0)
{
lean_object* v_unused_230_; lean_object* v_unused_231_; 
v_unused_230_ = lean_ctor_get(v___x_216_, 1);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v___x_216_, 0);
lean_dec(v_unused_231_);
v___x_223_ = v___x_216_;
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
else
{
lean_dec(v___x_216_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_225_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__1));
if (v_isShared_224_ == 0)
{
lean_ctor_set_tag(v___x_223_, 1);
lean_ctor_set(v___x_223_, 1, v___x_225_);
v___x_227_ = v___x_223_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_pos_217_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v___x_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
else
{
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_parse_x3f(lean_object* v_string_234_){
_start:
{
lean_object* v___f_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___f_235_ = ((lean_object*)(l_Std_Http_URI_parse_x3f___closed__0));
v___x_236_ = lean_string_to_utf8(v_string_234_);
v___x_237_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_235_, v___x_236_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v___x_238_; 
lean_dec_ref_known(v___x_237_, 1);
v___x_238_ = lean_box(0);
return v___x_238_;
}
else
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
v_a_239_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___x_237_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_237_);
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
static lean_object* _init_l_Std_Http_URI_parse_x21___closed__2(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_249_ = ((lean_object*)(l_Std_Http_URI_parse_x21___closed__1));
v___x_250_ = lean_unsigned_to_nat(12u);
v___x_251_ = lean_unsigned_to_nat(157u);
v___x_252_ = ((lean_object*)(l_Std_Http_URI_parse_x21___closed__0));
v___x_253_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x21___closed__0));
v___x_254_ = l_mkPanicMessageWithDecl(v___x_253_, v___x_252_, v___x_251_, v___x_250_, v___x_249_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_parse_x21(lean_object* v_string_255_){
_start:
{
lean_object* v___f_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___f_256_ = ((lean_object*)(l_Std_Http_URI_parse_x3f___closed__0));
v___x_257_ = lean_string_to_utf8(v_string_255_);
v___x_258_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_256_, v___x_257_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec_ref_known(v___x_258_, 1);
v___x_259_ = l_Std_Http_instInhabitedURI_default;
v___x_260_ = lean_obj_once(&l_Std_Http_URI_parse_x21___closed__2, &l_Std_Http_URI_parse_x21___closed__2_once, _init_l_Std_Http_URI_parse_x21___closed__2);
v___x_261_ = l_panic___redArg(v___x_259_, v___x_260_);
return v___x_261_;
}
else
{
lean_object* v_a_262_; 
v_a_262_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_a_262_);
lean_dec_ref_known(v___x_258_, 1);
return v_a_262_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parse_x3f___lam__0(lean_object* v___x_263_, uint8_t v___x_264_, lean_object* v___y_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Std_Http_URI_Parser_parsePath(v___x_263_, v___x_264_, v___x_264_, v___y_265_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_pos_267_; lean_object* v_array_268_; lean_object* v_idx_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v_pos_267_ = lean_ctor_get(v___x_266_, 0);
v_array_268_ = lean_ctor_get(v_pos_267_, 0);
v_idx_269_ = lean_ctor_get(v_pos_267_, 1);
v___x_270_ = lean_byte_array_size(v_array_268_);
v___x_271_ = lean_nat_dec_lt(v_idx_269_, v___x_270_);
if (v___x_271_ == 0)
{
return v___x_266_;
}
else
{
lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_279_; 
lean_inc(v_pos_267_);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_279_ == 0)
{
lean_object* v_unused_280_; lean_object* v_unused_281_; 
v_unused_280_ = lean_ctor_get(v___x_266_, 1);
lean_dec(v_unused_280_);
v_unused_281_ = lean_ctor_get(v___x_266_, 0);
lean_dec(v_unused_281_);
v___x_273_ = v___x_266_;
v_isShared_274_ = v_isSharedCheck_279_;
goto v_resetjp_272_;
}
else
{
lean_dec(v___x_266_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_279_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_275_; lean_object* v___x_277_; 
v___x_275_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__1));
if (v_isShared_274_ == 0)
{
lean_ctor_set_tag(v___x_273_, 1);
lean_ctor_set(v___x_273_, 1, v___x_275_);
v___x_277_ = v___x_273_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_pos_267_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
else
{
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parse_x3f___lam__0___boxed(lean_object* v___x_282_, lean_object* v___x_283_, lean_object* v___y_284_){
_start:
{
uint8_t v___x_275__boxed_285_; lean_object* v_res_286_; 
v___x_275__boxed_285_ = lean_unbox(v___x_283_);
v_res_286_ = l_Std_Http_URI_Path_parse_x3f___lam__0(v___x_282_, v___x_275__boxed_285_, v___y_284_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parse_x3f(lean_object* v_s_291_){
_start:
{
lean_object* v___f_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___f_292_ = ((lean_object*)(l_Std_Http_URI_Path_parse_x3f___closed__0));
v___x_293_ = lean_string_to_utf8(v_s_291_);
v___x_294_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_292_, v___x_293_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v___x_295_; 
lean_dec_ref_known(v___x_294_, 1);
v___x_295_ = lean_box(0);
return v___x_295_;
}
else
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
v_a_296_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v___x_294_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_294_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_296_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parseOrRoot(lean_object* v_s_304_){
_start:
{
lean_object* v___f_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___f_305_ = ((lean_object*)(l_Std_Http_URI_Path_parse_x3f___closed__0));
v___x_306_ = lean_string_to_utf8(v_s_304_);
v___x_307_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_305_, v___x_306_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v___x_308_; 
lean_dec_ref_known(v___x_307_, 1);
v___x_308_ = ((lean_object*)(l_Std_Http_RequestTarget_pathOrRoot___closed__1));
return v___x_308_;
}
else
{
lean_object* v_a_309_; 
v_a_309_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_309_);
lean_dec_ref_known(v___x_307_, 1);
return v_a_309_;
}
}
}
lean_object* runtime_initialize_Std_Http_Data_URI_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_URI_Parser(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_URI(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

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
uint16_t l_Std_Http_URI_Scheme_defaultPort(lean_object*);
lean_object* l_Std_Http_URI_Parser_parseURIReference(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Std_Http_instInhabitedRequestTarget_default;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_Http_URI_Query_insert(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Http_URI_Query_empty;
lean_object* l_Std_Http_URI_Parser_parsePath(lean_object*, uint8_t, uint8_t, lean_object*);
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
static const lean_array_object l_Std_Http_RequestTarget_pathOrRoot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_RequestTarget_pathOrRoot___closed__0 = (const lean_object*)&l_Std_Http_RequestTarget_pathOrRoot___closed__0_value;
static const lean_ctor_object l_Std_Http_RequestTarget_pathOrRoot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_RequestTarget_pathOrRoot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Http_RequestTarget_pathOrRoot___closed__1 = (const lean_object*)&l_Std_Http_RequestTarget_pathOrRoot___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_pathOrRoot(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_pathOrRoot___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_setQueryParam(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_setQueryParam___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URIReference_parse_x3f___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_URIReference_parse_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_URIReference_parse_x3f___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_RequestTarget_parse_x3f___closed__0_value)} };
static const lean_object* l_Std_Http_URIReference_parse_x3f___closed__0 = (const lean_object*)&l_Std_Http_URIReference_parse_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_URIReference_parse_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URIReference_parse_x3f___boxed(lean_object*);
static const lean_string_object l_Std_Http_URIReference_parse_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Std.Http.URIReference.parse!"};
static const lean_object* l_Std_Http_URIReference_parse_x21___closed__0 = (const lean_object*)&l_Std_Http_URIReference_parse_x21___closed__0_value;
static const lean_string_object l_Std_Http_URIReference_parse_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "invalid URI reference"};
static const lean_object* l_Std_Http_URIReference_parse_x21___closed__1 = (const lean_object*)&l_Std_Http_URIReference_parse_x21___closed__1_value;
static lean_once_cell_t l_Std_Http_URIReference_parse_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URIReference_parse_x21___closed__2;
LEAN_EXPORT lean_object* l_Std_Http_URIReference_parse_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URIReference_parse_x21___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Std_Http_URI_port(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_port___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_host_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_originTarget(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_originTarget___boxed(lean_object*);
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
lean_dec_ref_known(v___x_59_, 1);
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
lean_dec_ref_known(v___x_59_, 1);
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
lean_dec_ref_known(v___x_81_, 1);
goto v___jp_70_;
}
else
{
lean_object* v_a_82_; 
v_a_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_a_82_);
lean_dec_ref_known(v___x_81_, 1);
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
v___x_73_ = lean_unsigned_to_nat(55u);
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
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_pathOrRoot(lean_object* v_x_90_){
_start:
{
switch(lean_obj_tag(v_x_90_))
{
case 0:
{
lean_object* v_path_91_; 
v_path_91_ = lean_ctor_get(v_x_90_, 0);
lean_inc_ref(v_path_91_);
return v_path_91_;
}
case 1:
{
lean_object* v_uri_92_; lean_object* v_path_93_; 
v_uri_92_ = lean_ctor_get(v_x_90_, 0);
v_path_93_ = lean_ctor_get(v_uri_92_, 2);
lean_inc_ref(v_path_93_);
return v_path_93_;
}
default: 
{
lean_object* v___x_94_; 
v___x_94_ = ((lean_object*)(l_Std_Http_RequestTarget_pathOrRoot___closed__1));
return v___x_94_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_pathOrRoot___boxed(lean_object* v_x_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_Http_RequestTarget_pathOrRoot(v_x_95_);
lean_dec(v_x_95_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_setQueryParam(lean_object* v_target_97_, lean_object* v_key_98_, lean_object* v_value_99_){
_start:
{
switch(lean_obj_tag(v_target_97_))
{
case 0:
{
lean_object* v_path_100_; lean_object* v_query_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_114_; 
v_path_100_ = lean_ctor_get(v_target_97_, 0);
v_query_101_ = lean_ctor_get(v_target_97_, 1);
v_isSharedCheck_114_ = !lean_is_exclusive(v_target_97_);
if (v_isSharedCheck_114_ == 0)
{
v___x_103_ = v_target_97_;
v_isShared_104_ = v_isSharedCheck_114_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_query_101_);
lean_inc(v_path_100_);
lean_dec(v_target_97_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_114_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___y_106_; 
if (lean_obj_tag(v_query_101_) == 0)
{
lean_object* v___x_112_; 
v___x_112_ = l_Std_Http_URI_Query_empty;
v___y_106_ = v___x_112_;
goto v___jp_105_;
}
else
{
lean_object* v_val_113_; 
v_val_113_ = lean_ctor_get(v_query_101_, 0);
lean_inc(v_val_113_);
lean_dec_ref_known(v_query_101_, 1);
v___y_106_ = v_val_113_;
goto v___jp_105_;
}
v___jp_105_:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
v___x_107_ = l_Std_Http_URI_Query_insert(v___y_106_, v_key_98_, v_value_99_);
v___x_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 1, v___x_108_);
v___x_110_ = v___x_103_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_path_100_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v___x_108_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
case 1:
{
lean_object* v_uri_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_140_; 
v_uri_115_ = lean_ctor_get(v_target_97_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v_target_97_);
if (v_isSharedCheck_140_ == 0)
{
v___x_117_ = v_target_97_;
v_isShared_118_ = v_isSharedCheck_140_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_uri_115_);
lean_dec(v_target_97_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_140_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v_scheme_119_; lean_object* v_authority_120_; lean_object* v_path_121_; lean_object* v_query_122_; lean_object* v_fragment_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_139_; 
v_scheme_119_ = lean_ctor_get(v_uri_115_, 0);
v_authority_120_ = lean_ctor_get(v_uri_115_, 1);
v_path_121_ = lean_ctor_get(v_uri_115_, 2);
v_query_122_ = lean_ctor_get(v_uri_115_, 3);
v_fragment_123_ = lean_ctor_get(v_uri_115_, 4);
v_isSharedCheck_139_ = !lean_is_exclusive(v_uri_115_);
if (v_isSharedCheck_139_ == 0)
{
v___x_125_ = v_uri_115_;
v_isShared_126_ = v_isSharedCheck_139_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_fragment_123_);
lean_inc(v_query_122_);
lean_inc(v_path_121_);
lean_inc(v_authority_120_);
lean_inc(v_scheme_119_);
lean_dec(v_uri_115_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_139_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___y_128_; 
if (lean_obj_tag(v_query_122_) == 0)
{
lean_object* v___x_137_; 
v___x_137_ = l_Std_Http_URI_Query_empty;
v___y_128_ = v___x_137_;
goto v___jp_127_;
}
else
{
lean_object* v_val_138_; 
v_val_138_ = lean_ctor_get(v_query_122_, 0);
lean_inc(v_val_138_);
lean_dec_ref_known(v_query_122_, 1);
v___y_128_ = v_val_138_;
goto v___jp_127_;
}
v___jp_127_:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_132_; 
v___x_129_ = l_Std_Http_URI_Query_insert(v___y_128_, v_key_98_, v_value_99_);
v___x_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 3, v___x_130_);
v___x_132_ = v___x_125_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_scheme_119_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v_authority_120_);
lean_ctor_set(v_reuseFailAlloc_136_, 2, v_path_121_);
lean_ctor_set(v_reuseFailAlloc_136_, 3, v___x_130_);
lean_ctor_set(v_reuseFailAlloc_136_, 4, v_fragment_123_);
v___x_132_ = v_reuseFailAlloc_136_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_134_; 
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v___x_132_);
v___x_134_ = v___x_117_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
}
}
default: 
{
return v_target_97_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_setQueryParam___boxed(lean_object* v_target_141_, lean_object* v_key_142_, lean_object* v_value_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Std_Http_RequestTarget_setQueryParam(v_target_141_, v_key_142_, v_value_143_);
lean_dec_ref(v_value_143_);
lean_dec_ref(v_key_142_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_parse_x3f___lam__0(lean_object* v___x_145_, lean_object* v___y_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Std_Http_URI_Parser_parseURIReference(v___x_145_, v___y_146_);
if (lean_obj_tag(v___x_147_) == 0)
{
lean_object* v_pos_148_; lean_object* v_array_149_; lean_object* v_idx_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v_pos_148_ = lean_ctor_get(v___x_147_, 0);
v_array_149_ = lean_ctor_get(v_pos_148_, 0);
v_idx_150_ = lean_ctor_get(v_pos_148_, 1);
v___x_151_ = lean_byte_array_size(v_array_149_);
v___x_152_ = lean_nat_dec_lt(v_idx_150_, v___x_151_);
if (v___x_152_ == 0)
{
return v___x_147_;
}
else
{
lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_160_; 
lean_inc(v_pos_148_);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_160_ == 0)
{
lean_object* v_unused_161_; lean_object* v_unused_162_; 
v_unused_161_ = lean_ctor_get(v___x_147_, 1);
lean_dec(v_unused_161_);
v_unused_162_ = lean_ctor_get(v___x_147_, 0);
lean_dec(v_unused_162_);
v___x_154_ = v___x_147_;
v_isShared_155_ = v_isSharedCheck_160_;
goto v_resetjp_153_;
}
else
{
lean_dec(v___x_147_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_160_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_156_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__1));
if (v_isShared_155_ == 0)
{
lean_ctor_set_tag(v___x_154_, 1);
lean_ctor_set(v___x_154_, 1, v___x_156_);
v___x_158_ = v___x_154_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_pos_148_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v___x_156_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
else
{
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_parse_x3f(lean_object* v_string_165_){
_start:
{
lean_object* v___f_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___f_166_ = ((lean_object*)(l_Std_Http_URIReference_parse_x3f___closed__0));
v___x_167_ = lean_string_to_utf8(v_string_165_);
v___x_168_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_166_, v___x_167_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v___x_169_; 
lean_dec_ref_known(v___x_168_, 1);
v___x_169_ = lean_box(0);
return v___x_169_;
}
else
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
v_a_170_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v___x_168_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_168_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_parse_x3f___boxed(lean_object* v_string_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Std_Http_URIReference_parse_x3f(v_string_178_);
lean_dec_ref(v_string_178_);
return v_res_179_;
}
}
static lean_object* _init_l_Std_Http_URIReference_parse_x21___closed__2(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_182_ = ((lean_object*)(l_Std_Http_URIReference_parse_x21___closed__1));
v___x_183_ = lean_unsigned_to_nat(12u);
v___x_184_ = lean_unsigned_to_nat(106u);
v___x_185_ = ((lean_object*)(l_Std_Http_URIReference_parse_x21___closed__0));
v___x_186_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x21___closed__0));
v___x_187_ = l_mkPanicMessageWithDecl(v___x_186_, v___x_185_, v___x_184_, v___x_183_, v___x_182_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_parse_x21(lean_object* v_string_188_){
_start:
{
lean_object* v___f_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___f_189_ = ((lean_object*)(l_Std_Http_URIReference_parse_x3f___closed__0));
v___x_190_ = lean_string_to_utf8(v_string_188_);
v___x_191_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_189_, v___x_190_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec_ref_known(v___x_191_, 1);
v___x_192_ = l_Std_Http_instInhabitedURIReference_default;
v___x_193_ = lean_obj_once(&l_Std_Http_URIReference_parse_x21___closed__2, &l_Std_Http_URIReference_parse_x21___closed__2_once, _init_l_Std_Http_URIReference_parse_x21___closed__2);
v___x_194_ = l_panic___redArg(v___x_192_, v___x_193_);
return v___x_194_;
}
else
{
lean_object* v_a_195_; 
v_a_195_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_a_195_);
lean_dec_ref_known(v___x_191_, 1);
return v_a_195_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_parse_x21___boxed(lean_object* v_string_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Std_Http_URIReference_parse_x21(v_string_196_);
lean_dec_ref(v_string_196_);
return v_res_197_;
}
}
uint16_t l_Std_Http_URI_port(lean_object* v_uri_198_){
_start:
{
lean_object* v_authority_199_; 
v_authority_199_ = lean_ctor_get(v_uri_198_, 1);
if (lean_obj_tag(v_authority_199_) == 0)
{
lean_object* v_scheme_200_; uint16_t v___x_201_; 
v_scheme_200_ = lean_ctor_get(v_uri_198_, 0);
v___x_201_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_200_);
return v___x_201_;
}
else
{
lean_object* v_val_202_; lean_object* v_port_203_; 
v_val_202_ = lean_ctor_get(v_authority_199_, 0);
v_port_203_ = lean_ctor_get(v_val_202_, 2);
if (lean_obj_tag(v_port_203_) == 2)
{
uint16_t v_port_204_; 
v_port_204_ = lean_ctor_get_uint16(v_port_203_, 0);
return v_port_204_;
}
else
{
lean_object* v_scheme_205_; uint16_t v___x_206_; 
v_scheme_205_ = lean_ctor_get(v_uri_198_, 0);
v___x_206_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_205_);
return v___x_206_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_URI_port_0interp(lean_interpreter_value* stack)
{
lean_object* v_uri_198_ = stack[0].m_obj;
uint16_t v_res_207_;
v_res_207_ = l_Std_Http_URI_port(v_uri_198_);
stack->m_num = v_res_207_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_port___boxed(lean_object* v_uri_208_){
_start:
{
uint16_t v_res_209_; lean_object* v_r_210_; 
v_res_209_ = l_Std_Http_URI_port(v_uri_208_);
lean_dec_ref(v_uri_208_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_host_x3f(lean_object* v_uri_211_){
_start:
{
lean_object* v_authority_212_; 
v_authority_212_ = lean_ctor_get(v_uri_211_, 1);
lean_inc(v_authority_212_);
lean_dec_ref(v_uri_211_);
if (lean_obj_tag(v_authority_212_) == 0)
{
lean_object* v___x_213_; 
v___x_213_ = lean_box(0);
return v___x_213_;
}
else
{
lean_object* v_val_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_222_; 
v_val_214_ = lean_ctor_get(v_authority_212_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v_authority_212_);
if (v_isSharedCheck_222_ == 0)
{
v___x_216_ = v_authority_212_;
v_isShared_217_ = v_isSharedCheck_222_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_val_214_);
lean_dec(v_authority_212_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_222_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v_host_218_; lean_object* v___x_220_; 
v_host_218_ = lean_ctor_get(v_val_214_, 1);
lean_inc_ref(v_host_218_);
lean_dec(v_val_214_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v_host_218_);
v___x_220_ = v___x_216_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_host_218_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_originTarget(lean_object* v_uri_223_){
_start:
{
lean_object* v_path_224_; lean_object* v_query_225_; lean_object* v___x_226_; 
v_path_224_ = lean_ctor_get(v_uri_223_, 2);
v_query_225_ = lean_ctor_get(v_uri_223_, 3);
lean_inc(v_query_225_);
lean_inc_ref(v_path_224_);
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v_path_224_);
lean_ctor_set(v___x_226_, 1, v_query_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_originTarget___boxed(lean_object* v_uri_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Std_Http_URI_originTarget(v_uri_227_);
lean_dec_ref(v_uri_227_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_parse_x3f___lam__0(lean_object* v___x_229_, lean_object* v___y_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Std_Http_URI_Parser_parseURI(v___x_229_, v___y_230_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_pos_232_; lean_object* v_array_233_; lean_object* v_idx_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v_pos_232_ = lean_ctor_get(v___x_231_, 0);
v_array_233_ = lean_ctor_get(v_pos_232_, 0);
v_idx_234_ = lean_ctor_get(v_pos_232_, 1);
v___x_235_ = lean_byte_array_size(v_array_233_);
v___x_236_ = lean_nat_dec_lt(v_idx_234_, v___x_235_);
if (v___x_236_ == 0)
{
return v___x_231_;
}
else
{
lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_244_; 
lean_inc(v_pos_232_);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_244_ == 0)
{
lean_object* v_unused_245_; lean_object* v_unused_246_; 
v_unused_245_ = lean_ctor_get(v___x_231_, 1);
lean_dec(v_unused_245_);
v_unused_246_ = lean_ctor_get(v___x_231_, 0);
lean_dec(v_unused_246_);
v___x_238_ = v___x_231_;
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
else
{
lean_dec(v___x_231_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_240_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__1));
if (v_isShared_239_ == 0)
{
lean_ctor_set_tag(v___x_238_, 1);
lean_ctor_set(v___x_238_, 1, v___x_240_);
v___x_242_ = v___x_238_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_pos_232_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
else
{
return v___x_231_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_parse_x3f(lean_object* v_string_249_){
_start:
{
lean_object* v___f_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___f_250_ = ((lean_object*)(l_Std_Http_URI_parse_x3f___closed__0));
v___x_251_ = lean_string_to_utf8(v_string_249_);
v___x_252_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_250_, v___x_251_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v___x_253_; 
lean_dec_ref_known(v___x_252_, 1);
v___x_253_ = lean_box(0);
return v___x_253_;
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
v_a_254_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_252_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_252_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_parse_x3f___boxed(lean_object* v_string_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Std_Http_URI_parse_x3f(v_string_262_);
lean_dec_ref(v_string_262_);
return v_res_263_;
}
}
static lean_object* _init_l_Std_Http_URI_parse_x21___closed__2(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_266_ = ((lean_object*)(l_Std_Http_URI_parse_x21___closed__1));
v___x_267_ = lean_unsigned_to_nat(12u);
v___x_268_ = lean_unsigned_to_nat(157u);
v___x_269_ = ((lean_object*)(l_Std_Http_URI_parse_x21___closed__0));
v___x_270_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x21___closed__0));
v___x_271_ = l_mkPanicMessageWithDecl(v___x_270_, v___x_269_, v___x_268_, v___x_267_, v___x_266_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_parse_x21(lean_object* v_string_272_){
_start:
{
lean_object* v___f_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___f_273_ = ((lean_object*)(l_Std_Http_URI_parse_x3f___closed__0));
v___x_274_ = lean_string_to_utf8(v_string_272_);
v___x_275_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_273_, v___x_274_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
lean_dec_ref_known(v___x_275_, 1);
v___x_276_ = l_Std_Http_instInhabitedURI_default;
v___x_277_ = lean_obj_once(&l_Std_Http_URI_parse_x21___closed__2, &l_Std_Http_URI_parse_x21___closed__2_once, _init_l_Std_Http_URI_parse_x21___closed__2);
v___x_278_ = l_panic___redArg(v___x_276_, v___x_277_);
return v___x_278_;
}
else
{
lean_object* v_a_279_; 
v_a_279_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_279_);
lean_dec_ref_known(v___x_275_, 1);
return v_a_279_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_parse_x21___boxed(lean_object* v_string_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Std_Http_URI_parse_x21(v_string_280_);
lean_dec_ref(v_string_280_);
return v_res_281_;
}
}
lean_object* l_Std_Http_URI_Path_parse_x3f___lam__0(lean_object* v___x_282_, uint8_t v___x_283_, lean_object* v___y_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Std_Http_URI_Parser_parsePath(v___x_282_, v___x_283_, v___x_283_, v___y_284_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_pos_286_; lean_object* v_array_287_; lean_object* v_idx_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v_pos_286_ = lean_ctor_get(v___x_285_, 0);
v_array_287_ = lean_ctor_get(v_pos_286_, 0);
v_idx_288_ = lean_ctor_get(v_pos_286_, 1);
v___x_289_ = lean_byte_array_size(v_array_287_);
v___x_290_ = lean_nat_dec_lt(v_idx_288_, v___x_289_);
if (v___x_290_ == 0)
{
return v___x_285_;
}
else
{
lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_298_; 
lean_inc(v_pos_286_);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_298_ == 0)
{
lean_object* v_unused_299_; lean_object* v_unused_300_; 
v_unused_299_ = lean_ctor_get(v___x_285_, 1);
lean_dec(v_unused_299_);
v_unused_300_ = lean_ctor_get(v___x_285_, 0);
lean_dec(v_unused_300_);
v___x_292_ = v___x_285_;
v_isShared_293_ = v_isSharedCheck_298_;
goto v_resetjp_291_;
}
else
{
lean_dec(v___x_285_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_298_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_294_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__1));
if (v_isShared_293_ == 0)
{
lean_ctor_set_tag(v___x_292_, 1);
lean_ctor_set(v___x_292_, 1, v___x_294_);
v___x_296_ = v___x_292_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_pos_286_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
else
{
return v___x_285_;
}
}
}
LEAN_EXPORT void l_Std_Http_URI_Path_parse_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_282_ = stack[0].m_obj;
uint8_t v___x_283_ = stack[1].m_num;
lean_object* v___y_284_ = stack[2].m_obj;
lean_object* v_res_301_;
v_res_301_ = l_Std_Http_URI_Path_parse_x3f___lam__0(v___x_282_, v___x_283_, v___y_284_);
stack->m_obj
 = v_res_301_;
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parse_x3f___lam__0___boxed(lean_object* v___x_302_, lean_object* v___x_303_, lean_object* v___y_304_){
_start:
{
uint8_t v___x_274__boxed_305_; lean_object* v_res_306_; 
v___x_274__boxed_305_ = lean_unbox(v___x_303_);
v_res_306_ = l_Std_Http_URI_Path_parse_x3f___lam__0(v___x_302_, v___x_274__boxed_305_, v___y_304_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parse_x3f(lean_object* v_s_311_){
_start:
{
lean_object* v___f_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___f_312_ = ((lean_object*)(l_Std_Http_URI_Path_parse_x3f___closed__0));
v___x_313_ = lean_string_to_utf8(v_s_311_);
v___x_314_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_312_, v___x_313_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v___x_315_; 
lean_dec_ref_known(v___x_314_, 1);
v___x_315_ = lean_box(0);
return v___x_315_;
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
v_a_316_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_314_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_314_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parse_x3f___boxed(lean_object* v_s_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Std_Http_URI_Path_parse_x3f(v_s_324_);
lean_dec_ref(v_s_324_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parseOrRoot(lean_object* v_s_326_){
_start:
{
lean_object* v___f_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___f_327_ = ((lean_object*)(l_Std_Http_URI_Path_parse_x3f___closed__0));
v___x_328_ = lean_string_to_utf8(v_s_326_);
v___x_329_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_327_, v___x_328_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v___x_330_; 
lean_dec_ref_known(v___x_329_, 1);
v___x_330_ = ((lean_object*)(l_Std_Http_RequestTarget_pathOrRoot___closed__1));
return v___x_330_;
}
else
{
lean_object* v_a_331_; 
v_a_331_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_a_331_);
lean_dec_ref_known(v___x_329_, 1);
return v_a_331_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parseOrRoot___boxed(lean_object* v_s_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Std_Http_URI_Path_parseOrRoot(v_s_332_);
lean_dec_ref(v_s_332_);
return v_res_333_;
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

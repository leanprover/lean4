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
static const lean_ctor_object l_Std_Http_RequestTarget_parse_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*9 + 0, .m_other = 9, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(64) << 1) | 1)),((lean_object*)(((size_t)(253) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1))}};
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
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_parse_x3f(lean_object* v_string_29_){
_start:
{
lean_object* v___f_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___f_30_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x3f___closed__1));
v___x_31_ = lean_string_to_utf8(v_string_29_);
v___x_32_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_30_, v___x_31_);
if (lean_obj_tag(v___x_32_) == 0)
{
lean_object* v___x_33_; 
lean_dec_ref_known(v___x_32_, 1);
v___x_33_ = lean_box(0);
return v___x_33_;
}
else
{
lean_object* v_a_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_41_; 
v_a_34_ = lean_ctor_get(v___x_32_, 0);
v_isSharedCheck_41_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_41_ == 0)
{
v___x_36_ = v___x_32_;
v_isShared_37_ = v_isSharedCheck_41_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_a_34_);
lean_dec(v___x_32_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_41_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_39_; 
if (v_isShared_37_ == 0)
{
v___x_39_ = v___x_36_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_a_34_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
return v___x_39_;
}
}
}
}
}
static lean_object* _init_l_Std_Http_RequestTarget_parse_x21___closed__3(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_45_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x21___closed__2));
v___x_46_ = lean_unsigned_to_nat(12u);
v___x_47_ = lean_unsigned_to_nat(45u);
v___x_48_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x21___closed__1));
v___x_49_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x21___closed__0));
v___x_50_ = l_mkPanicMessageWithDecl(v___x_49_, v___x_48_, v___x_47_, v___x_46_, v___x_45_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_parse_x21(lean_object* v_string_51_){
_start:
{
lean_object* v___f_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___f_52_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x3f___closed__1));
v___x_53_ = lean_string_to_utf8(v_string_51_);
v___x_54_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_52_, v___x_53_);
if (lean_obj_tag(v___x_54_) == 0)
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
lean_dec_ref_known(v___x_54_, 1);
v___x_55_ = l_Std_Http_instInhabitedRequestTarget_default;
v___x_56_ = lean_obj_once(&l_Std_Http_RequestTarget_parse_x21___closed__3, &l_Std_Http_RequestTarget_parse_x21___closed__3_once, _init_l_Std_Http_RequestTarget_parse_x21___closed__3);
v___x_57_ = l_panic___redArg(v___x_55_, v___x_56_);
return v___x_57_;
}
else
{
lean_object* v_a_58_; 
v_a_58_ = lean_ctor_get(v___x_54_, 0);
lean_inc(v_a_58_);
lean_dec_ref_known(v___x_54_, 1);
return v_a_58_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_originForm_x21(lean_object* v_path_61_){
_start:
{
lean_object* v___x_62_; lean_object* v___f_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_62_ = l_Std_Http_instInhabitedRequestTarget_default;
v___f_72_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x3f___closed__1));
lean_inc_ref(v_path_61_);
v___x_73_ = lean_string_to_utf8(v_path_61_);
v___x_74_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_72_, v___x_73_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_dec_ref_known(v___x_74_, 1);
goto v___jp_63_;
}
else
{
lean_object* v_a_75_; 
v_a_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_a_75_);
lean_dec_ref_known(v___x_74_, 1);
if (lean_obj_tag(v_a_75_) == 0)
{
lean_dec_ref(v_path_61_);
return v_a_75_;
}
else
{
lean_dec(v_a_75_);
goto v___jp_63_;
}
}
v___jp_63_:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_64_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x21___closed__0));
v___x_65_ = ((lean_object*)(l_Std_Http_RequestTarget_originForm_x21___closed__0));
v___x_66_ = lean_unsigned_to_nat(55u);
v___x_67_ = lean_unsigned_to_nat(9u);
v___x_68_ = ((lean_object*)(l_Std_Http_RequestTarget_originForm_x21___closed__1));
v___x_69_ = lean_string_append(v___x_68_, v_path_61_);
lean_dec_ref(v_path_61_);
v___x_70_ = l_mkPanicMessageWithDecl(v___x_64_, v___x_65_, v___x_66_, v___x_67_, v___x_69_);
lean_dec_ref(v___x_69_);
v___x_71_ = l_panic___redArg(v___x_62_, v___x_70_);
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_pathOrRoot(lean_object* v_x_81_){
_start:
{
switch(lean_obj_tag(v_x_81_))
{
case 0:
{
lean_object* v_path_82_; 
v_path_82_ = lean_ctor_get(v_x_81_, 0);
lean_inc_ref(v_path_82_);
return v_path_82_;
}
case 1:
{
lean_object* v_uri_83_; lean_object* v_path_84_; 
v_uri_83_ = lean_ctor_get(v_x_81_, 0);
v_path_84_ = lean_ctor_get(v_uri_83_, 2);
lean_inc_ref(v_path_84_);
return v_path_84_;
}
default: 
{
lean_object* v___x_85_; 
v___x_85_ = ((lean_object*)(l_Std_Http_RequestTarget_pathOrRoot___closed__1));
return v___x_85_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_pathOrRoot___boxed(lean_object* v_x_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Std_Http_RequestTarget_pathOrRoot(v_x_86_);
lean_dec(v_x_86_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_RequestTarget_setQueryParam(lean_object* v_target_88_, lean_object* v_key_89_, lean_object* v_value_90_){
_start:
{
switch(lean_obj_tag(v_target_88_))
{
case 0:
{
lean_object* v_path_91_; lean_object* v_query_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_105_; 
v_path_91_ = lean_ctor_get(v_target_88_, 0);
v_query_92_ = lean_ctor_get(v_target_88_, 1);
v_isSharedCheck_105_ = !lean_is_exclusive(v_target_88_);
if (v_isSharedCheck_105_ == 0)
{
v___x_94_ = v_target_88_;
v_isShared_95_ = v_isSharedCheck_105_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_query_92_);
lean_inc(v_path_91_);
lean_dec(v_target_88_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_105_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___y_97_; 
if (lean_obj_tag(v_query_92_) == 0)
{
lean_object* v___x_103_; 
v___x_103_ = l_Std_Http_URI_Query_empty;
v___y_97_ = v___x_103_;
goto v___jp_96_;
}
else
{
lean_object* v_val_104_; 
v_val_104_ = lean_ctor_get(v_query_92_, 0);
lean_inc(v_val_104_);
lean_dec_ref_known(v_query_92_, 1);
v___y_97_ = v_val_104_;
goto v___jp_96_;
}
v___jp_96_:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_101_; 
v___x_98_ = l_Std_Http_URI_Query_insert(v___y_97_, v_key_89_, v_value_90_);
v___x_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 1, v___x_99_);
v___x_101_ = v___x_94_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_path_91_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v___x_99_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
case 1:
{
lean_object* v_uri_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_131_; 
v_uri_106_ = lean_ctor_get(v_target_88_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v_target_88_);
if (v_isSharedCheck_131_ == 0)
{
v___x_108_ = v_target_88_;
v_isShared_109_ = v_isSharedCheck_131_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_uri_106_);
lean_dec(v_target_88_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_131_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v_scheme_110_; lean_object* v_authority_111_; lean_object* v_path_112_; lean_object* v_query_113_; lean_object* v_fragment_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_130_; 
v_scheme_110_ = lean_ctor_get(v_uri_106_, 0);
v_authority_111_ = lean_ctor_get(v_uri_106_, 1);
v_path_112_ = lean_ctor_get(v_uri_106_, 2);
v_query_113_ = lean_ctor_get(v_uri_106_, 3);
v_fragment_114_ = lean_ctor_get(v_uri_106_, 4);
v_isSharedCheck_130_ = !lean_is_exclusive(v_uri_106_);
if (v_isSharedCheck_130_ == 0)
{
v___x_116_ = v_uri_106_;
v_isShared_117_ = v_isSharedCheck_130_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_fragment_114_);
lean_inc(v_query_113_);
lean_inc(v_path_112_);
lean_inc(v_authority_111_);
lean_inc(v_scheme_110_);
lean_dec(v_uri_106_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_130_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___y_119_; 
if (lean_obj_tag(v_query_113_) == 0)
{
lean_object* v___x_128_; 
v___x_128_ = l_Std_Http_URI_Query_empty;
v___y_119_ = v___x_128_;
goto v___jp_118_;
}
else
{
lean_object* v_val_129_; 
v_val_129_ = lean_ctor_get(v_query_113_, 0);
lean_inc(v_val_129_);
lean_dec_ref_known(v_query_113_, 1);
v___y_119_ = v_val_129_;
goto v___jp_118_;
}
v___jp_118_:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_120_ = l_Std_Http_URI_Query_insert(v___y_119_, v_key_89_, v_value_90_);
v___x_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 3, v___x_121_);
v___x_123_ = v___x_116_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_scheme_110_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_authority_111_);
lean_ctor_set(v_reuseFailAlloc_127_, 2, v_path_112_);
lean_ctor_set(v_reuseFailAlloc_127_, 3, v___x_121_);
lean_ctor_set(v_reuseFailAlloc_127_, 4, v_fragment_114_);
v___x_123_ = v_reuseFailAlloc_127_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
lean_object* v___x_125_; 
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 0, v___x_123_);
v___x_125_ = v___x_108_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_123_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_value_90_);
lean_dec_ref(v_key_89_);
return v_target_88_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_parse_x3f___lam__0(lean_object* v___x_132_, lean_object* v___y_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Std_Http_URI_Parser_parseURIReference(v___x_132_, v___y_133_);
if (lean_obj_tag(v___x_134_) == 0)
{
lean_object* v_pos_135_; lean_object* v_array_136_; lean_object* v_idx_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v_pos_135_ = lean_ctor_get(v___x_134_, 0);
v_array_136_ = lean_ctor_get(v_pos_135_, 0);
v_idx_137_ = lean_ctor_get(v_pos_135_, 1);
v___x_138_ = lean_byte_array_size(v_array_136_);
v___x_139_ = lean_nat_dec_lt(v_idx_137_, v___x_138_);
if (v___x_139_ == 0)
{
return v___x_134_;
}
else
{
lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_147_; 
lean_inc(v_pos_135_);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_147_ == 0)
{
lean_object* v_unused_148_; lean_object* v_unused_149_; 
v_unused_148_ = lean_ctor_get(v___x_134_, 1);
lean_dec(v_unused_148_);
v_unused_149_ = lean_ctor_get(v___x_134_, 0);
lean_dec(v_unused_149_);
v___x_141_ = v___x_134_;
v_isShared_142_ = v_isSharedCheck_147_;
goto v_resetjp_140_;
}
else
{
lean_dec(v___x_134_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_147_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_143_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__1));
if (v_isShared_142_ == 0)
{
lean_ctor_set_tag(v___x_141_, 1);
lean_ctor_set(v___x_141_, 1, v___x_143_);
v___x_145_ = v___x_141_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_pos_135_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v___x_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
else
{
return v___x_134_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_parse_x3f(lean_object* v_string_152_){
_start:
{
lean_object* v___f_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___f_153_ = ((lean_object*)(l_Std_Http_URIReference_parse_x3f___closed__0));
v___x_154_ = lean_string_to_utf8(v_string_152_);
v___x_155_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_153_, v___x_154_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v___x_156_; 
lean_dec_ref_known(v___x_155_, 1);
v___x_156_ = lean_box(0);
return v___x_156_;
}
else
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
v_a_157_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v___x_155_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_155_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_157_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
}
static lean_object* _init_l_Std_Http_URIReference_parse_x21___closed__2(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_167_ = ((lean_object*)(l_Std_Http_URIReference_parse_x21___closed__1));
v___x_168_ = lean_unsigned_to_nat(12u);
v___x_169_ = lean_unsigned_to_nat(106u);
v___x_170_ = ((lean_object*)(l_Std_Http_URIReference_parse_x21___closed__0));
v___x_171_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x21___closed__0));
v___x_172_ = l_mkPanicMessageWithDecl(v___x_171_, v___x_170_, v___x_169_, v___x_168_, v___x_167_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URIReference_parse_x21(lean_object* v_string_173_){
_start:
{
lean_object* v___f_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___f_174_ = ((lean_object*)(l_Std_Http_URIReference_parse_x3f___closed__0));
v___x_175_ = lean_string_to_utf8(v_string_173_);
v___x_176_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_174_, v___x_175_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
lean_dec_ref_known(v___x_176_, 1);
v___x_177_ = l_Std_Http_instInhabitedURIReference_default;
v___x_178_ = lean_obj_once(&l_Std_Http_URIReference_parse_x21___closed__2, &l_Std_Http_URIReference_parse_x21___closed__2_once, _init_l_Std_Http_URIReference_parse_x21___closed__2);
v___x_179_ = l_panic___redArg(v___x_177_, v___x_178_);
return v___x_179_;
}
else
{
lean_object* v_a_180_; 
v_a_180_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_a_180_);
lean_dec_ref_known(v___x_176_, 1);
return v_a_180_;
}
}
}
LEAN_EXPORT uint16_t l_Std_Http_URI_port(lean_object* v_uri_181_){
_start:
{
lean_object* v_authority_182_; 
v_authority_182_ = lean_ctor_get(v_uri_181_, 1);
if (lean_obj_tag(v_authority_182_) == 0)
{
lean_object* v_scheme_183_; uint16_t v___x_184_; 
v_scheme_183_ = lean_ctor_get(v_uri_181_, 0);
v___x_184_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_183_);
return v___x_184_;
}
else
{
lean_object* v_val_185_; lean_object* v_port_186_; 
v_val_185_ = lean_ctor_get(v_authority_182_, 0);
v_port_186_ = lean_ctor_get(v_val_185_, 2);
if (lean_obj_tag(v_port_186_) == 2)
{
uint16_t v_port_187_; 
v_port_187_ = lean_ctor_get_uint16(v_port_186_, 0);
return v_port_187_;
}
else
{
lean_object* v_scheme_188_; uint16_t v___x_189_; 
v_scheme_188_ = lean_ctor_get(v_uri_181_, 0);
v___x_189_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_188_);
return v___x_189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_port___boxed(lean_object* v_uri_190_){
_start:
{
uint16_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_Std_Http_URI_port(v_uri_190_);
lean_dec_ref(v_uri_190_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_host_x3f(lean_object* v_uri_193_){
_start:
{
lean_object* v_authority_194_; 
v_authority_194_ = lean_ctor_get(v_uri_193_, 1);
lean_inc(v_authority_194_);
lean_dec_ref(v_uri_193_);
if (lean_obj_tag(v_authority_194_) == 0)
{
lean_object* v___x_195_; 
v___x_195_ = lean_box(0);
return v___x_195_;
}
else
{
lean_object* v_val_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_204_; 
v_val_196_ = lean_ctor_get(v_authority_194_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v_authority_194_);
if (v_isSharedCheck_204_ == 0)
{
v___x_198_ = v_authority_194_;
v_isShared_199_ = v_isSharedCheck_204_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_val_196_);
lean_dec(v_authority_194_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_204_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v_host_200_; lean_object* v___x_202_; 
v_host_200_ = lean_ctor_get(v_val_196_, 1);
lean_inc_ref(v_host_200_);
lean_dec(v_val_196_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v_host_200_);
v___x_202_ = v___x_198_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_host_200_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_originTarget(lean_object* v_uri_205_){
_start:
{
lean_object* v_path_206_; lean_object* v_query_207_; lean_object* v___x_208_; 
v_path_206_ = lean_ctor_get(v_uri_205_, 2);
v_query_207_ = lean_ctor_get(v_uri_205_, 3);
lean_inc(v_query_207_);
lean_inc_ref(v_path_206_);
v___x_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_208_, 0, v_path_206_);
lean_ctor_set(v___x_208_, 1, v_query_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_originTarget___boxed(lean_object* v_uri_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Std_Http_URI_originTarget(v_uri_209_);
lean_dec_ref(v_uri_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_parse_x3f___lam__0(lean_object* v___x_211_, lean_object* v___y_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Std_Http_URI_Parser_parseURI(v___x_211_, v___y_212_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_pos_214_; lean_object* v_array_215_; lean_object* v_idx_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v_pos_214_ = lean_ctor_get(v___x_213_, 0);
v_array_215_ = lean_ctor_get(v_pos_214_, 0);
v_idx_216_ = lean_ctor_get(v_pos_214_, 1);
v___x_217_ = lean_byte_array_size(v_array_215_);
v___x_218_ = lean_nat_dec_lt(v_idx_216_, v___x_217_);
if (v___x_218_ == 0)
{
return v___x_213_;
}
else
{
lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_226_; 
lean_inc(v_pos_214_);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_226_ == 0)
{
lean_object* v_unused_227_; lean_object* v_unused_228_; 
v_unused_227_ = lean_ctor_get(v___x_213_, 1);
lean_dec(v_unused_227_);
v_unused_228_ = lean_ctor_get(v___x_213_, 0);
lean_dec(v_unused_228_);
v___x_220_ = v___x_213_;
v_isShared_221_ = v_isSharedCheck_226_;
goto v_resetjp_219_;
}
else
{
lean_dec(v___x_213_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_226_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_222_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__1));
if (v_isShared_221_ == 0)
{
lean_ctor_set_tag(v___x_220_, 1);
lean_ctor_set(v___x_220_, 1, v___x_222_);
v___x_224_ = v___x_220_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_pos_214_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
else
{
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_parse_x3f(lean_object* v_string_231_){
_start:
{
lean_object* v___f_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___f_232_ = ((lean_object*)(l_Std_Http_URI_parse_x3f___closed__0));
v___x_233_ = lean_string_to_utf8(v_string_231_);
v___x_234_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_232_, v___x_233_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v___x_235_; 
lean_dec_ref_known(v___x_234_, 1);
v___x_235_ = lean_box(0);
return v___x_235_;
}
else
{
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_243_; 
v_a_236_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_243_ == 0)
{
v___x_238_ = v___x_234_;
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_234_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_236_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
}
static lean_object* _init_l_Std_Http_URI_parse_x21___closed__2(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_246_ = ((lean_object*)(l_Std_Http_URI_parse_x21___closed__1));
v___x_247_ = lean_unsigned_to_nat(12u);
v___x_248_ = lean_unsigned_to_nat(157u);
v___x_249_ = ((lean_object*)(l_Std_Http_URI_parse_x21___closed__0));
v___x_250_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x21___closed__0));
v___x_251_ = l_mkPanicMessageWithDecl(v___x_250_, v___x_249_, v___x_248_, v___x_247_, v___x_246_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_parse_x21(lean_object* v_string_252_){
_start:
{
lean_object* v___f_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___f_253_ = ((lean_object*)(l_Std_Http_URI_parse_x3f___closed__0));
v___x_254_ = lean_string_to_utf8(v_string_252_);
v___x_255_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_253_, v___x_254_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec_ref_known(v___x_255_, 1);
v___x_256_ = l_Std_Http_instInhabitedURI_default;
v___x_257_ = lean_obj_once(&l_Std_Http_URI_parse_x21___closed__2, &l_Std_Http_URI_parse_x21___closed__2_once, _init_l_Std_Http_URI_parse_x21___closed__2);
v___x_258_ = l_panic___redArg(v___x_256_, v___x_257_);
return v___x_258_;
}
else
{
lean_object* v_a_259_; 
v_a_259_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_a_259_);
lean_dec_ref_known(v___x_255_, 1);
return v_a_259_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parse_x3f___lam__0(lean_object* v___x_260_, uint8_t v___x_261_, lean_object* v___y_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Std_Http_URI_Parser_parsePath(v___x_260_, v___x_261_, v___x_261_, v___y_262_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_pos_264_; lean_object* v_array_265_; lean_object* v_idx_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v_pos_264_ = lean_ctor_get(v___x_263_, 0);
v_array_265_ = lean_ctor_get(v_pos_264_, 0);
v_idx_266_ = lean_ctor_get(v_pos_264_, 1);
v___x_267_ = lean_byte_array_size(v_array_265_);
v___x_268_ = lean_nat_dec_lt(v_idx_266_, v___x_267_);
if (v___x_268_ == 0)
{
return v___x_263_;
}
else
{
lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_276_; 
lean_inc(v_pos_264_);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_276_ == 0)
{
lean_object* v_unused_277_; lean_object* v_unused_278_; 
v_unused_277_ = lean_ctor_get(v___x_263_, 1);
lean_dec(v_unused_277_);
v_unused_278_ = lean_ctor_get(v___x_263_, 0);
lean_dec(v_unused_278_);
v___x_270_ = v___x_263_;
v_isShared_271_ = v_isSharedCheck_276_;
goto v_resetjp_269_;
}
else
{
lean_dec(v___x_263_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_276_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_272_ = ((lean_object*)(l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__1));
if (v_isShared_271_ == 0)
{
lean_ctor_set_tag(v___x_270_, 1);
lean_ctor_set(v___x_270_, 1, v___x_272_);
v___x_274_ = v___x_270_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_pos_264_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v___x_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
else
{
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parse_x3f___lam__0___boxed(lean_object* v___x_279_, lean_object* v___x_280_, lean_object* v___y_281_){
_start:
{
uint8_t v___x_263__boxed_282_; lean_object* v_res_283_; 
v___x_263__boxed_282_ = lean_unbox(v___x_280_);
v_res_283_ = l_Std_Http_URI_Path_parse_x3f___lam__0(v___x_279_, v___x_263__boxed_282_, v___y_281_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parse_x3f(lean_object* v_s_288_){
_start:
{
lean_object* v___f_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___f_289_ = ((lean_object*)(l_Std_Http_URI_Path_parse_x3f___closed__0));
v___x_290_ = lean_string_to_utf8(v_s_288_);
v___x_291_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_289_, v___x_290_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v___x_292_; 
lean_dec_ref_known(v___x_291_, 1);
v___x_292_ = lean_box(0);
return v___x_292_;
}
else
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_300_; 
v_a_293_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_300_ == 0)
{
v___x_295_ = v___x_291_;
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_291_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_293_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Path_parseOrRoot(lean_object* v_s_301_){
_start:
{
lean_object* v___f_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___f_302_ = ((lean_object*)(l_Std_Http_URI_Path_parse_x3f___closed__0));
v___x_303_ = lean_string_to_utf8(v_s_301_);
v___x_304_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_302_, v___x_303_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v___x_305_; 
lean_dec_ref_known(v___x_304_, 1);
v___x_305_ = ((lean_object*)(l_Std_Http_RequestTarget_pathOrRoot___closed__1));
return v___x_305_;
}
else
{
lean_object* v_a_306_; 
v_a_306_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_a_306_);
lean_dec_ref_known(v___x_304_, 1);
return v_a_306_;
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

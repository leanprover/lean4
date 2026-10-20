// Lean compiler output
// Module: Std.Http.Protocol.H1.Event
// Imports: public import Std.Time public import Std.Http.Data public import Std.Http.Internal public import Std.Http.Protocol.H1.Parser public import Std.Http.Protocol.H1.Config public import Std.Http.Protocol.H1.Message public import Std.Http.Protocol.H1.Error
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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_instReprHead(uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Std_Http_Protocol_H1_instReprError_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorIdx___impl(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorElim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_endHeaders_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_endHeaders_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_endHeaders_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_needMoreData_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_needMoreData_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_needMoreData_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_failed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_failed_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_failed_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_close_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_close_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_close_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_closeBody_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_closeBody_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_closeBody_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_needAnswer_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_needAnswer_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_needAnswer_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_next_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_next_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_next_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_continue_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_continue_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_continue_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Protocol_H1_instInhabitedEvent_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent_default___redArg___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instInhabitedEvent_default___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent_default___redArg();
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent_default(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent___redArg();
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent___boxed(lean_object*);
static const lean_string_object l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__0 = (const lean_object*)&l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__1 = (const lean_object*)&l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__1_value;
static const lean_string_object l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__2 = (const lean_object*)&l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__3 = (const lean_object*)&l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_instReprEvent_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Std.Http.Protocol.H1.Event.close"};
static const lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__0_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprEvent_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__0_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__1_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprEvent_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Http.Protocol.H1.Event.closeBody"};
static const lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr___closed__2 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__2_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprEvent_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__2_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr___closed__3 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__3_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprEvent_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Std.Http.Protocol.H1.Event.needAnswer"};
static const lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr___closed__4 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__4_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprEvent_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__4_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr___closed__5 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__5_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprEvent_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Std.Http.Protocol.H1.Event.next"};
static const lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr___closed__6 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__6_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprEvent_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__6_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr___closed__7 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__7_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprEvent_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Std.Http.Protocol.H1.Event.continue"};
static const lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr___closed__8 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__8_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprEvent_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__8_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr___closed__9 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__9_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprEvent_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Std.Http.Protocol.H1.Event.endHeaders"};
static const lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr___closed__10 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__10_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprEvent_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__10_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr___closed__11 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__11_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprEvent_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__11_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr___closed__12 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__12_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13;
static lean_once_cell_t l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14;
static const lean_string_object l_Std_Http_Protocol_H1_instReprEvent_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Std.Http.Protocol.H1.Event.needMoreData"};
static const lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr___closed__15 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__15_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprEvent_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__15_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr___closed__16 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__16_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprEvent_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__16_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr___closed__17 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__17_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprEvent_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Std.Http.Protocol.H1.Event.failed"};
static const lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr___closed__18 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__18_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprEvent_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__18_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr___closed__19 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__19_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprEvent_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__19_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr___closed__20 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__20_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprEvent(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprEvent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorIdx___impl___redArg(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorIdx___impl___redArg___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Std_Http_Protocol_H1_Event_ctorIdx___impl___redArg(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorIdx___impl(uint8_t v_dir_5_, lean_object* v_x_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_tag_nat(v_x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorIdx___impl___boxed(lean_object* v_dir_8_, lean_object* v_x_9_){
_start:
{
uint8_t v_dir_boxed_10_; lean_object* v_res_11_; 
v_dir_boxed_10_ = lean_unbox(v_dir_8_);
v_res_11_ = l_Std_Http_Protocol_H1_Event_ctorIdx___impl(v_dir_boxed_10_, v_x_9_);
lean_dec(v_x_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorElim___redArg(lean_object* v_t_12_, lean_object* v_k_13_){
_start:
{
switch(lean_obj_tag(v_t_12_))
{
case 0:
{
lean_object* v_head_14_; lean_object* v___x_15_; 
v_head_14_ = lean_ctor_get(v_t_12_, 0);
lean_inc(v_head_14_);
lean_dec_ref_known(v_t_12_, 1);
v___x_15_ = lean_apply_1(v_k_13_, v_head_14_);
return v___x_15_;
}
case 1:
{
lean_object* v_size_16_; lean_object* v___x_17_; 
v_size_16_ = lean_ctor_get(v_t_12_, 0);
lean_inc(v_size_16_);
lean_dec_ref_known(v_t_12_, 1);
v___x_17_ = lean_apply_1(v_k_13_, v_size_16_);
return v___x_17_;
}
case 2:
{
lean_object* v_err_18_; lean_object* v___x_19_; 
v_err_18_ = lean_ctor_get(v_t_12_, 0);
lean_inc(v_err_18_);
lean_dec_ref_known(v_t_12_, 1);
v___x_19_ = lean_apply_1(v_k_13_, v_err_18_);
return v___x_19_;
}
default: 
{
lean_dec(v_t_12_);
return v_k_13_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorElim(uint8_t v_dir_20_, lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_23_, v_k_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorElim___boxed(lean_object* v_dir_27_, lean_object* v_motive_28_, lean_object* v_ctorIdx_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_k_32_){
_start:
{
uint8_t v_dir_boxed_33_; lean_object* v_res_34_; 
v_dir_boxed_33_ = lean_unbox(v_dir_27_);
v_res_34_ = l_Std_Http_Protocol_H1_Event_ctorElim(v_dir_boxed_33_, v_motive_28_, v_ctorIdx_29_, v_t_30_, v_h_31_, v_k_32_);
lean_dec(v_ctorIdx_29_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_endHeaders_elim___redArg(lean_object* v_t_35_, lean_object* v_endHeaders_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_35_, v_endHeaders_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_endHeaders_elim(uint8_t v_dir_38_, lean_object* v_motive_39_, lean_object* v_t_40_, lean_object* v_h_41_, lean_object* v_endHeaders_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_40_, v_endHeaders_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_endHeaders_elim___boxed(lean_object* v_dir_44_, lean_object* v_motive_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_endHeaders_48_){
_start:
{
uint8_t v_dir_boxed_49_; lean_object* v_res_50_; 
v_dir_boxed_49_ = lean_unbox(v_dir_44_);
v_res_50_ = l_Std_Http_Protocol_H1_Event_endHeaders_elim(v_dir_boxed_49_, v_motive_45_, v_t_46_, v_h_47_, v_endHeaders_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_needMoreData_elim___redArg(lean_object* v_t_51_, lean_object* v_needMoreData_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_51_, v_needMoreData_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_needMoreData_elim(uint8_t v_dir_54_, lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_needMoreData_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_56_, v_needMoreData_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_needMoreData_elim___boxed(lean_object* v_dir_60_, lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_needMoreData_64_){
_start:
{
uint8_t v_dir_boxed_65_; lean_object* v_res_66_; 
v_dir_boxed_65_ = lean_unbox(v_dir_60_);
v_res_66_ = l_Std_Http_Protocol_H1_Event_needMoreData_elim(v_dir_boxed_65_, v_motive_61_, v_t_62_, v_h_63_, v_needMoreData_64_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_failed_elim___redArg(lean_object* v_t_67_, lean_object* v_failed_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_67_, v_failed_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_failed_elim(uint8_t v_dir_70_, lean_object* v_motive_71_, lean_object* v_t_72_, lean_object* v_h_73_, lean_object* v_failed_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_72_, v_failed_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_failed_elim___boxed(lean_object* v_dir_76_, lean_object* v_motive_77_, lean_object* v_t_78_, lean_object* v_h_79_, lean_object* v_failed_80_){
_start:
{
uint8_t v_dir_boxed_81_; lean_object* v_res_82_; 
v_dir_boxed_81_ = lean_unbox(v_dir_76_);
v_res_82_ = l_Std_Http_Protocol_H1_Event_failed_elim(v_dir_boxed_81_, v_motive_77_, v_t_78_, v_h_79_, v_failed_80_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_close_elim___redArg(lean_object* v_t_83_, lean_object* v_close_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_83_, v_close_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_close_elim(uint8_t v_dir_86_, lean_object* v_motive_87_, lean_object* v_t_88_, lean_object* v_h_89_, lean_object* v_close_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_88_, v_close_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_close_elim___boxed(lean_object* v_dir_92_, lean_object* v_motive_93_, lean_object* v_t_94_, lean_object* v_h_95_, lean_object* v_close_96_){
_start:
{
uint8_t v_dir_boxed_97_; lean_object* v_res_98_; 
v_dir_boxed_97_ = lean_unbox(v_dir_92_);
v_res_98_ = l_Std_Http_Protocol_H1_Event_close_elim(v_dir_boxed_97_, v_motive_93_, v_t_94_, v_h_95_, v_close_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_closeBody_elim___redArg(lean_object* v_t_99_, lean_object* v_closeBody_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_99_, v_closeBody_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_closeBody_elim(uint8_t v_dir_102_, lean_object* v_motive_103_, lean_object* v_t_104_, lean_object* v_h_105_, lean_object* v_closeBody_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_104_, v_closeBody_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_closeBody_elim___boxed(lean_object* v_dir_108_, lean_object* v_motive_109_, lean_object* v_t_110_, lean_object* v_h_111_, lean_object* v_closeBody_112_){
_start:
{
uint8_t v_dir_boxed_113_; lean_object* v_res_114_; 
v_dir_boxed_113_ = lean_unbox(v_dir_108_);
v_res_114_ = l_Std_Http_Protocol_H1_Event_closeBody_elim(v_dir_boxed_113_, v_motive_109_, v_t_110_, v_h_111_, v_closeBody_112_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_needAnswer_elim___redArg(lean_object* v_t_115_, lean_object* v_needAnswer_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_115_, v_needAnswer_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_needAnswer_elim(uint8_t v_dir_118_, lean_object* v_motive_119_, lean_object* v_t_120_, lean_object* v_h_121_, lean_object* v_needAnswer_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_120_, v_needAnswer_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_needAnswer_elim___boxed(lean_object* v_dir_124_, lean_object* v_motive_125_, lean_object* v_t_126_, lean_object* v_h_127_, lean_object* v_needAnswer_128_){
_start:
{
uint8_t v_dir_boxed_129_; lean_object* v_res_130_; 
v_dir_boxed_129_ = lean_unbox(v_dir_124_);
v_res_130_ = l_Std_Http_Protocol_H1_Event_needAnswer_elim(v_dir_boxed_129_, v_motive_125_, v_t_126_, v_h_127_, v_needAnswer_128_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_next_elim___redArg(lean_object* v_t_131_, lean_object* v_next_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_131_, v_next_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_next_elim(uint8_t v_dir_134_, lean_object* v_motive_135_, lean_object* v_t_136_, lean_object* v_h_137_, lean_object* v_next_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_136_, v_next_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_next_elim___boxed(lean_object* v_dir_140_, lean_object* v_motive_141_, lean_object* v_t_142_, lean_object* v_h_143_, lean_object* v_next_144_){
_start:
{
uint8_t v_dir_boxed_145_; lean_object* v_res_146_; 
v_dir_boxed_145_ = lean_unbox(v_dir_140_);
v_res_146_ = l_Std_Http_Protocol_H1_Event_next_elim(v_dir_boxed_145_, v_motive_141_, v_t_142_, v_h_143_, v_next_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_continue_elim___redArg(lean_object* v_t_147_, lean_object* v_continue_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_147_, v_continue_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_continue_elim(uint8_t v_dir_150_, lean_object* v_motive_151_, lean_object* v_t_152_, lean_object* v_h_153_, lean_object* v_continue_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_152_, v_continue_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_continue_elim___boxed(lean_object* v_dir_156_, lean_object* v_motive_157_, lean_object* v_t_158_, lean_object* v_h_159_, lean_object* v_continue_160_){
_start:
{
uint8_t v_dir_boxed_161_; lean_object* v_res_162_; 
v_dir_boxed_161_ = lean_unbox(v_dir_156_);
v_res_162_ = l_Std_Http_Protocol_H1_Event_continue_elim(v_dir_boxed_161_, v_motive_157_, v_t_158_, v_h_159_, v_continue_160_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent_default___redArg(){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = ((lean_object*)(l_Std_Http_Protocol_H1_instInhabitedEvent_default___redArg___closed__0));
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent_default___redArg___boxed(lean_object* v___dummy_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Std_Http_Protocol_H1_instInhabitedEvent_default___redArg();
return v_res_168_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0(void){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Std_Http_Protocol_H1_instInhabitedEvent_default___redArg();
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent_default(uint8_t v_dir_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lean_obj_once(&l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0, &l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0_once, _init_l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent_default___boxed(lean_object* v_dir_172_){
_start:
{
uint8_t v_dir_boxed_173_; lean_object* v_res_174_; 
v_dir_boxed_173_ = lean_unbox(v_dir_172_);
v_res_174_ = l_Std_Http_Protocol_H1_instInhabitedEvent_default(v_dir_boxed_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent___redArg(){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lean_obj_once(&l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0, &l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0_once, _init_l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent___redArg___boxed(lean_object* v___dummy_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_Http_Protocol_H1_instInhabitedEvent___redArg();
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent(uint8_t v_a_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_obj_once(&l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0, &l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0_once, _init_l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent___boxed(lean_object* v_a_181_){
_start:
{
uint8_t v_a_13__boxed_182_; lean_object* v_res_183_; 
v_a_13__boxed_182_ = lean_unbox(v_a_181_);
v_res_183_ = l_Std_Http_Protocol_H1_instInhabitedEvent(v_a_13__boxed_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0(lean_object* v_x_190_, lean_object* v_x_191_){
_start:
{
if (lean_obj_tag(v_x_190_) == 0)
{
lean_object* v___x_192_; 
v___x_192_ = ((lean_object*)(l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__1));
return v___x_192_;
}
else
{
lean_object* v_val_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_204_; 
v_val_193_ = lean_ctor_get(v_x_190_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v_x_190_);
if (v_isSharedCheck_204_ == 0)
{
v___x_195_ = v_x_190_;
v_isShared_196_ = v_isSharedCheck_204_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_val_193_);
lean_dec(v_x_190_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_204_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_197_ = ((lean_object*)(l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__3));
v___x_198_ = l_Nat_reprFast(v_val_193_);
if (v_isShared_196_ == 0)
{
lean_ctor_set_tag(v___x_195_, 3);
lean_ctor_set(v___x_195_, 0, v___x_198_);
v___x_200_ = v___x_195_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_198_);
v___x_200_ = v_reuseFailAlloc_203_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_197_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = l_Repr_addAppParen(v___x_201_, v_x_191_);
return v___x_202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___boxed(lean_object* v_x_205_, lean_object* v_x_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0(v_x_205_, v_x_206_);
lean_dec(v_x_206_);
return v_res_207_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lean_unsigned_to_nat(2u);
v___x_230_ = lean_nat_to_int(v___x_229_);
return v___x_230_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_unsigned_to_nat(1u);
v___x_232_ = lean_nat_to_int(v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr(uint8_t v_dir_245_, lean_object* v_x_246_, lean_object* v_prec_247_){
_start:
{
lean_object* v___y_249_; lean_object* v___y_256_; lean_object* v___y_263_; lean_object* v___y_270_; lean_object* v___y_277_; 
switch(lean_obj_tag(v_x_246_))
{
case 0:
{
lean_object* v_head_283_; lean_object* v___y_285_; lean_object* v___x_295_; uint8_t v___x_296_; 
v_head_283_ = lean_ctor_get(v_x_246_, 0);
lean_inc(v_head_283_);
lean_dec_ref_known(v_x_246_, 1);
v___x_295_ = lean_unsigned_to_nat(1024u);
v___x_296_ = lean_nat_dec_le(v___x_295_, v_prec_247_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
v___x_297_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13);
v___y_285_ = v___x_297_;
goto v___jp_284_;
}
else
{
lean_object* v___x_298_; 
v___x_298_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14);
v___y_285_ = v___x_298_;
goto v___jp_284_;
}
v___jp_284_:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_351__overap_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_286_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__12));
v___x_287_ = lean_unsigned_to_nat(1024u);
v___x_351__overap_288_ = l_Std_Http_Protocol_H1_instReprHead(v_dir_245_);
v___x_289_ = lean_apply_2(v___x_351__overap_288_, v_head_283_, v___x_287_);
v___x_290_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_286_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
lean_inc(v___y_285_);
v___x_291_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_291_, 0, v___y_285_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = 0;
v___x_293_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_293_, 0, v___x_291_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*1, v___x_292_);
v___x_294_ = l_Repr_addAppParen(v___x_293_, v_prec_247_);
return v___x_294_;
}
}
case 1:
{
lean_object* v_size_299_; lean_object* v___y_301_; lean_object* v___x_310_; uint8_t v___x_311_; 
v_size_299_ = lean_ctor_get(v_x_246_, 0);
lean_inc(v_size_299_);
lean_dec_ref_known(v_x_246_, 1);
v___x_310_ = lean_unsigned_to_nat(1024u);
v___x_311_ = lean_nat_dec_le(v___x_310_, v_prec_247_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; 
v___x_312_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13);
v___y_301_ = v___x_312_;
goto v___jp_300_;
}
else
{
lean_object* v___x_313_; 
v___x_313_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14);
v___y_301_ = v___x_313_;
goto v___jp_300_;
}
v___jp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_302_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__17));
v___x_303_ = lean_unsigned_to_nat(1024u);
v___x_304_ = l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0(v_size_299_, v___x_303_);
v___x_305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_302_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
lean_inc(v___y_301_);
v___x_306_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_306_, 0, v___y_301_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = 0;
v___x_308_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_308_, 0, v___x_306_);
lean_ctor_set_uint8(v___x_308_, sizeof(void*)*1, v___x_307_);
v___x_309_ = l_Repr_addAppParen(v___x_308_, v_prec_247_);
return v___x_309_;
}
}
case 2:
{
lean_object* v_err_314_; lean_object* v___y_316_; lean_object* v___x_325_; uint8_t v___x_326_; 
v_err_314_ = lean_ctor_get(v_x_246_, 0);
lean_inc(v_err_314_);
lean_dec_ref_known(v_x_246_, 1);
v___x_325_ = lean_unsigned_to_nat(1024u);
v___x_326_ = lean_nat_dec_le(v___x_325_, v_prec_247_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; 
v___x_327_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13);
v___y_316_ = v___x_327_;
goto v___jp_315_;
}
else
{
lean_object* v___x_328_; 
v___x_328_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14);
v___y_316_ = v___x_328_;
goto v___jp_315_;
}
v___jp_315_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_317_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__20));
v___x_318_ = lean_unsigned_to_nat(1024u);
v___x_319_ = l_Std_Http_Protocol_H1_instReprError_repr(v_err_314_, v___x_318_);
v___x_320_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_317_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
lean_inc(v___y_316_);
v___x_321_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_321_, 0, v___y_316_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v___x_322_ = 0;
v___x_323_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_323_, 0, v___x_321_);
lean_ctor_set_uint8(v___x_323_, sizeof(void*)*1, v___x_322_);
v___x_324_ = l_Repr_addAppParen(v___x_323_, v_prec_247_);
return v___x_324_;
}
}
case 3:
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = lean_unsigned_to_nat(1024u);
v___x_330_ = lean_nat_dec_le(v___x_329_, v_prec_247_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; 
v___x_331_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13);
v___y_249_ = v___x_331_;
goto v___jp_248_;
}
else
{
lean_object* v___x_332_; 
v___x_332_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14);
v___y_249_ = v___x_332_;
goto v___jp_248_;
}
}
case 4:
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = lean_unsigned_to_nat(1024u);
v___x_334_ = lean_nat_dec_le(v___x_333_, v_prec_247_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; 
v___x_335_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13);
v___y_256_ = v___x_335_;
goto v___jp_255_;
}
else
{
lean_object* v___x_336_; 
v___x_336_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14);
v___y_256_ = v___x_336_;
goto v___jp_255_;
}
}
case 5:
{
lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = lean_unsigned_to_nat(1024u);
v___x_338_ = lean_nat_dec_le(v___x_337_, v_prec_247_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; 
v___x_339_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13);
v___y_263_ = v___x_339_;
goto v___jp_262_;
}
else
{
lean_object* v___x_340_; 
v___x_340_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14);
v___y_263_ = v___x_340_;
goto v___jp_262_;
}
}
case 6:
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = lean_unsigned_to_nat(1024u);
v___x_342_ = lean_nat_dec_le(v___x_341_, v_prec_247_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; 
v___x_343_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13);
v___y_270_ = v___x_343_;
goto v___jp_269_;
}
else
{
lean_object* v___x_344_; 
v___x_344_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14);
v___y_270_ = v___x_344_;
goto v___jp_269_;
}
}
default: 
{
lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_345_ = lean_unsigned_to_nat(1024u);
v___x_346_ = lean_nat_dec_le(v___x_345_, v_prec_247_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; 
v___x_347_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13);
v___y_277_ = v___x_347_;
goto v___jp_276_;
}
else
{
lean_object* v___x_348_; 
v___x_348_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14);
v___y_277_ = v___x_348_;
goto v___jp_276_;
}
}
}
v___jp_248_:
{
lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_250_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__1));
lean_inc(v___y_249_);
v___x_251_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_251_, 0, v___y_249_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = 0;
v___x_253_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_253_, 0, v___x_251_);
lean_ctor_set_uint8(v___x_253_, sizeof(void*)*1, v___x_252_);
v___x_254_ = l_Repr_addAppParen(v___x_253_, v_prec_247_);
return v___x_254_;
}
v___jp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_257_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__3));
lean_inc(v___y_256_);
v___x_258_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_258_, 0, v___y_256_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = 0;
v___x_260_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_260_, 0, v___x_258_);
lean_ctor_set_uint8(v___x_260_, sizeof(void*)*1, v___x_259_);
v___x_261_ = l_Repr_addAppParen(v___x_260_, v_prec_247_);
return v___x_261_;
}
v___jp_262_:
{
lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_264_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__5));
lean_inc(v___y_263_);
v___x_265_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_265_, 0, v___y_263_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = 0;
v___x_267_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_267_, 0, v___x_265_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*1, v___x_266_);
v___x_268_ = l_Repr_addAppParen(v___x_267_, v_prec_247_);
return v___x_268_;
}
v___jp_269_:
{
lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_271_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__7));
lean_inc(v___y_270_);
v___x_272_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_272_, 0, v___y_270_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = 0;
v___x_274_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_274_, 0, v___x_272_);
lean_ctor_set_uint8(v___x_274_, sizeof(void*)*1, v___x_273_);
v___x_275_ = l_Repr_addAppParen(v___x_274_, v_prec_247_);
return v___x_275_;
}
v___jp_276_:
{
lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_278_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__9));
lean_inc(v___y_277_);
v___x_279_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_279_, 0, v___y_277_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v___x_280_ = 0;
v___x_281_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_281_, 0, v___x_279_);
lean_ctor_set_uint8(v___x_281_, sizeof(void*)*1, v___x_280_);
v___x_282_ = l_Repr_addAppParen(v___x_281_, v_prec_247_);
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr___boxed(lean_object* v_dir_349_, lean_object* v_x_350_, lean_object* v_prec_351_){
_start:
{
uint8_t v_dir_685__boxed_352_; lean_object* v_res_353_; 
v_dir_685__boxed_352_ = lean_unbox(v_dir_349_);
v_res_353_ = l_Std_Http_Protocol_H1_instReprEvent_repr(v_dir_685__boxed_352_, v_x_350_, v_prec_351_);
lean_dec(v_prec_351_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprEvent(uint8_t v_dir_354_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_box(v_dir_354_);
v___x_356_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_instReprEvent_repr___boxed), 3, 1);
lean_closure_set(v___x_356_, 0, v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprEvent___boxed(lean_object* v_dir_357_){
_start:
{
uint8_t v_dir_5__boxed_358_; lean_object* v_res_359_; 
v_dir_5__boxed_358_ = lean_unbox(v_dir_357_);
v_res_359_ = l_Std_Http_Protocol_H1_instReprEvent(v_dir_5__boxed_358_);
return v_res_359_;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Internal(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Parser(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Config(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Message(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Error(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Protocol_H1_Event(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Protocol_H1_Event(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time(uint8_t builtin);
lean_object* initialize_Std_Http_Data(uint8_t builtin);
lean_object* initialize_Std_Http_Internal(uint8_t builtin);
lean_object* initialize_Std_Http_Protocol_H1_Parser(uint8_t builtin);
lean_object* initialize_Std_Http_Protocol_H1_Config(uint8_t builtin);
lean_object* initialize_Std_Http_Protocol_H1_Message(uint8_t builtin);
lean_object* initialize_Std_Http_Protocol_H1_Error(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Protocol_H1_Event(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Protocol_H1_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Protocol_H1_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Protocol_H1_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Protocol_H1_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Event(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Protocol_H1_Event(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Protocol_H1_Event(builtin);
}
#ifdef __cplusplus
}
#endif

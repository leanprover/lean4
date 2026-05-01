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
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_instReprHead(uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Std_Http_Protocol_H1_instReprError_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorIdx(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorIdx___boxed(lean_object*, lean_object*);
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
static const lean_ctor_object l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent_default(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent_default___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorIdx___redArg(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
case 5:
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
case 6:
{
lean_object* v___x_8_; 
v___x_8_ = lean_unsigned_to_nat(6u);
return v___x_8_;
}
default: 
{
lean_object* v___x_9_; 
v___x_9_ = lean_unsigned_to_nat(7u);
return v___x_9_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorIdx___redArg___boxed(lean_object* v_x_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Std_Http_Protocol_H1_Event_ctorIdx___redArg(v_x_10_);
lean_dec(v_x_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorIdx(uint8_t v_dir_12_, lean_object* v_x_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Std_Http_Protocol_H1_Event_ctorIdx___redArg(v_x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorIdx___boxed(lean_object* v_dir_15_, lean_object* v_x_16_){
_start:
{
uint8_t v_dir_boxed_17_; lean_object* v_res_18_; 
v_dir_boxed_17_ = lean_unbox(v_dir_15_);
v_res_18_ = l_Std_Http_Protocol_H1_Event_ctorIdx(v_dir_boxed_17_, v_x_16_);
lean_dec(v_x_16_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorElim___redArg(lean_object* v_t_19_, lean_object* v_k_20_){
_start:
{
switch(lean_obj_tag(v_t_19_))
{
case 0:
{
lean_object* v_head_21_; lean_object* v___x_22_; 
v_head_21_ = lean_ctor_get(v_t_19_, 0);
lean_inc(v_head_21_);
lean_dec_ref(v_t_19_);
v___x_22_ = lean_apply_1(v_k_20_, v_head_21_);
return v___x_22_;
}
case 1:
{
lean_object* v_size_23_; lean_object* v___x_24_; 
v_size_23_ = lean_ctor_get(v_t_19_, 0);
lean_inc(v_size_23_);
lean_dec_ref(v_t_19_);
v___x_24_ = lean_apply_1(v_k_20_, v_size_23_);
return v___x_24_;
}
case 2:
{
lean_object* v_err_25_; lean_object* v___x_26_; 
v_err_25_ = lean_ctor_get(v_t_19_, 0);
lean_inc(v_err_25_);
lean_dec_ref(v_t_19_);
v___x_26_ = lean_apply_1(v_k_20_, v_err_25_);
return v___x_26_;
}
default: 
{
lean_dec(v_t_19_);
return v_k_20_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorElim(uint8_t v_dir_27_, lean_object* v_motive_28_, lean_object* v_ctorIdx_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_k_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_30_, v_k_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorElim___boxed(lean_object* v_dir_34_, lean_object* v_motive_35_, lean_object* v_ctorIdx_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_k_39_){
_start:
{
uint8_t v_dir_boxed_40_; lean_object* v_res_41_; 
v_dir_boxed_40_ = lean_unbox(v_dir_34_);
v_res_41_ = l_Std_Http_Protocol_H1_Event_ctorElim(v_dir_boxed_40_, v_motive_35_, v_ctorIdx_36_, v_t_37_, v_h_38_, v_k_39_);
lean_dec(v_ctorIdx_36_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_endHeaders_elim___redArg(lean_object* v_t_42_, lean_object* v_endHeaders_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_42_, v_endHeaders_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_endHeaders_elim(uint8_t v_dir_45_, lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_endHeaders_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_47_, v_endHeaders_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_endHeaders_elim___boxed(lean_object* v_dir_51_, lean_object* v_motive_52_, lean_object* v_t_53_, lean_object* v_h_54_, lean_object* v_endHeaders_55_){
_start:
{
uint8_t v_dir_boxed_56_; lean_object* v_res_57_; 
v_dir_boxed_56_ = lean_unbox(v_dir_51_);
v_res_57_ = l_Std_Http_Protocol_H1_Event_endHeaders_elim(v_dir_boxed_56_, v_motive_52_, v_t_53_, v_h_54_, v_endHeaders_55_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_needMoreData_elim___redArg(lean_object* v_t_58_, lean_object* v_needMoreData_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_58_, v_needMoreData_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_needMoreData_elim(uint8_t v_dir_61_, lean_object* v_motive_62_, lean_object* v_t_63_, lean_object* v_h_64_, lean_object* v_needMoreData_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_63_, v_needMoreData_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_needMoreData_elim___boxed(lean_object* v_dir_67_, lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_needMoreData_71_){
_start:
{
uint8_t v_dir_boxed_72_; lean_object* v_res_73_; 
v_dir_boxed_72_ = lean_unbox(v_dir_67_);
v_res_73_ = l_Std_Http_Protocol_H1_Event_needMoreData_elim(v_dir_boxed_72_, v_motive_68_, v_t_69_, v_h_70_, v_needMoreData_71_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_failed_elim___redArg(lean_object* v_t_74_, lean_object* v_failed_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_74_, v_failed_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_failed_elim(uint8_t v_dir_77_, lean_object* v_motive_78_, lean_object* v_t_79_, lean_object* v_h_80_, lean_object* v_failed_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_79_, v_failed_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_failed_elim___boxed(lean_object* v_dir_83_, lean_object* v_motive_84_, lean_object* v_t_85_, lean_object* v_h_86_, lean_object* v_failed_87_){
_start:
{
uint8_t v_dir_boxed_88_; lean_object* v_res_89_; 
v_dir_boxed_88_ = lean_unbox(v_dir_83_);
v_res_89_ = l_Std_Http_Protocol_H1_Event_failed_elim(v_dir_boxed_88_, v_motive_84_, v_t_85_, v_h_86_, v_failed_87_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_close_elim___redArg(lean_object* v_t_90_, lean_object* v_close_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_90_, v_close_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_close_elim(uint8_t v_dir_93_, lean_object* v_motive_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_close_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_95_, v_close_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_close_elim___boxed(lean_object* v_dir_99_, lean_object* v_motive_100_, lean_object* v_t_101_, lean_object* v_h_102_, lean_object* v_close_103_){
_start:
{
uint8_t v_dir_boxed_104_; lean_object* v_res_105_; 
v_dir_boxed_104_ = lean_unbox(v_dir_99_);
v_res_105_ = l_Std_Http_Protocol_H1_Event_close_elim(v_dir_boxed_104_, v_motive_100_, v_t_101_, v_h_102_, v_close_103_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_closeBody_elim___redArg(lean_object* v_t_106_, lean_object* v_closeBody_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_106_, v_closeBody_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_closeBody_elim(uint8_t v_dir_109_, lean_object* v_motive_110_, lean_object* v_t_111_, lean_object* v_h_112_, lean_object* v_closeBody_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_111_, v_closeBody_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_closeBody_elim___boxed(lean_object* v_dir_115_, lean_object* v_motive_116_, lean_object* v_t_117_, lean_object* v_h_118_, lean_object* v_closeBody_119_){
_start:
{
uint8_t v_dir_boxed_120_; lean_object* v_res_121_; 
v_dir_boxed_120_ = lean_unbox(v_dir_115_);
v_res_121_ = l_Std_Http_Protocol_H1_Event_closeBody_elim(v_dir_boxed_120_, v_motive_116_, v_t_117_, v_h_118_, v_closeBody_119_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_needAnswer_elim___redArg(lean_object* v_t_122_, lean_object* v_needAnswer_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_122_, v_needAnswer_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_needAnswer_elim(uint8_t v_dir_125_, lean_object* v_motive_126_, lean_object* v_t_127_, lean_object* v_h_128_, lean_object* v_needAnswer_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_127_, v_needAnswer_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_needAnswer_elim___boxed(lean_object* v_dir_131_, lean_object* v_motive_132_, lean_object* v_t_133_, lean_object* v_h_134_, lean_object* v_needAnswer_135_){
_start:
{
uint8_t v_dir_boxed_136_; lean_object* v_res_137_; 
v_dir_boxed_136_ = lean_unbox(v_dir_131_);
v_res_137_ = l_Std_Http_Protocol_H1_Event_needAnswer_elim(v_dir_boxed_136_, v_motive_132_, v_t_133_, v_h_134_, v_needAnswer_135_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_next_elim___redArg(lean_object* v_t_138_, lean_object* v_next_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_138_, v_next_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_next_elim(uint8_t v_dir_141_, lean_object* v_motive_142_, lean_object* v_t_143_, lean_object* v_h_144_, lean_object* v_next_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_143_, v_next_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_next_elim___boxed(lean_object* v_dir_147_, lean_object* v_motive_148_, lean_object* v_t_149_, lean_object* v_h_150_, lean_object* v_next_151_){
_start:
{
uint8_t v_dir_boxed_152_; lean_object* v_res_153_; 
v_dir_boxed_152_ = lean_unbox(v_dir_147_);
v_res_153_ = l_Std_Http_Protocol_H1_Event_next_elim(v_dir_boxed_152_, v_motive_148_, v_t_149_, v_h_150_, v_next_151_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_continue_elim___redArg(lean_object* v_t_154_, lean_object* v_continue_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_154_, v_continue_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_continue_elim(uint8_t v_dir_157_, lean_object* v_motive_158_, lean_object* v_t_159_, lean_object* v_h_160_, lean_object* v_continue_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_159_, v_continue_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_continue_elim___boxed(lean_object* v_dir_163_, lean_object* v_motive_164_, lean_object* v_t_165_, lean_object* v_h_166_, lean_object* v_continue_167_){
_start:
{
uint8_t v_dir_boxed_168_; lean_object* v_res_169_; 
v_dir_boxed_168_ = lean_unbox(v_dir_163_);
v_res_169_ = l_Std_Http_Protocol_H1_Event_continue_elim(v_dir_boxed_168_, v_motive_164_, v_t_165_, v_h_166_, v_continue_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent_default(uint8_t v_dir_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = ((lean_object*)(l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0));
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent_default___boxed(lean_object* v_dir_174_){
_start:
{
uint8_t v_dir_boxed_175_; lean_object* v_res_176_; 
v_dir_boxed_175_ = lean_unbox(v_dir_174_);
v_res_176_ = l_Std_Http_Protocol_H1_instInhabitedEvent_default(v_dir_boxed_175_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent(uint8_t v_a_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Std_Http_Protocol_H1_instInhabitedEvent_default(v_a_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent___boxed(lean_object* v_a_179_){
_start:
{
uint8_t v_a_5__boxed_180_; lean_object* v_res_181_; 
v_a_5__boxed_180_ = lean_unbox(v_a_179_);
v_res_181_ = l_Std_Http_Protocol_H1_instInhabitedEvent(v_a_5__boxed_180_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0(lean_object* v_x_188_, lean_object* v_x_189_){
_start:
{
if (lean_obj_tag(v_x_188_) == 0)
{
lean_object* v___x_190_; 
v___x_190_ = ((lean_object*)(l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__1));
return v___x_190_;
}
else
{
lean_object* v_val_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_202_; 
v_val_191_ = lean_ctor_get(v_x_188_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v_x_188_);
if (v_isSharedCheck_202_ == 0)
{
v___x_193_ = v_x_188_;
v_isShared_194_ = v_isSharedCheck_202_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_val_191_);
lean_dec(v_x_188_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_202_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_198_; 
v___x_195_ = ((lean_object*)(l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__3));
v___x_196_ = l_Nat_reprFast(v_val_191_);
if (v_isShared_194_ == 0)
{
lean_ctor_set_tag(v___x_193_, 3);
lean_ctor_set(v___x_193_, 0, v___x_196_);
v___x_198_ = v___x_193_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_196_);
v___x_198_ = v_reuseFailAlloc_201_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_195_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v___x_200_ = l_Repr_addAppParen(v___x_199_, v_x_189_);
return v___x_200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___boxed(lean_object* v_x_203_, lean_object* v_x_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0(v_x_203_, v_x_204_);
lean_dec(v_x_204_);
return v_res_205_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_unsigned_to_nat(2u);
v___x_228_ = lean_nat_to_int(v___x_227_);
return v___x_228_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lean_unsigned_to_nat(1u);
v___x_230_ = lean_nat_to_int(v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr(uint8_t v_dir_243_, lean_object* v_x_244_, lean_object* v_prec_245_){
_start:
{
lean_object* v___y_247_; lean_object* v___y_254_; lean_object* v___y_261_; lean_object* v___y_268_; lean_object* v___y_275_; 
switch(lean_obj_tag(v_x_244_))
{
case 0:
{
lean_object* v_head_281_; lean_object* v___y_283_; lean_object* v___x_293_; uint8_t v___x_294_; 
v_head_281_ = lean_ctor_get(v_x_244_, 0);
lean_inc(v_head_281_);
lean_dec_ref(v_x_244_);
v___x_293_ = lean_unsigned_to_nat(1024u);
v___x_294_ = lean_nat_dec_le(v___x_293_, v_prec_245_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; 
v___x_295_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13);
v___y_283_ = v___x_295_;
goto v___jp_282_;
}
else
{
lean_object* v___x_296_; 
v___x_296_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14);
v___y_283_ = v___x_296_;
goto v___jp_282_;
}
v___jp_282_:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_358__overap_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_284_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__12));
v___x_285_ = lean_unsigned_to_nat(1024u);
v___x_358__overap_286_ = l_Std_Http_Protocol_H1_instReprHead(v_dir_243_);
v___x_287_ = lean_apply_2(v___x_358__overap_286_, v_head_281_, v___x_285_);
v___x_288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_284_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
lean_inc(v___y_283_);
v___x_289_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_289_, 0, v___y_283_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = 0;
v___x_291_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_291_, 0, v___x_289_);
lean_ctor_set_uint8(v___x_291_, sizeof(void*)*1, v___x_290_);
v___x_292_ = l_Repr_addAppParen(v___x_291_, v_prec_245_);
return v___x_292_;
}
}
case 1:
{
lean_object* v_size_297_; lean_object* v___y_299_; lean_object* v___x_308_; uint8_t v___x_309_; 
v_size_297_ = lean_ctor_get(v_x_244_, 0);
lean_inc(v_size_297_);
lean_dec_ref(v_x_244_);
v___x_308_ = lean_unsigned_to_nat(1024u);
v___x_309_ = lean_nat_dec_le(v___x_308_, v_prec_245_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; 
v___x_310_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13);
v___y_299_ = v___x_310_;
goto v___jp_298_;
}
else
{
lean_object* v___x_311_; 
v___x_311_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14);
v___y_299_ = v___x_311_;
goto v___jp_298_;
}
v___jp_298_:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_300_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__17));
v___x_301_ = lean_unsigned_to_nat(1024u);
v___x_302_ = l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0(v_size_297_, v___x_301_);
v___x_303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_300_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
lean_inc(v___y_299_);
v___x_304_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_304_, 0, v___y_299_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = 0;
v___x_306_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_306_, 0, v___x_304_);
lean_ctor_set_uint8(v___x_306_, sizeof(void*)*1, v___x_305_);
v___x_307_ = l_Repr_addAppParen(v___x_306_, v_prec_245_);
return v___x_307_;
}
}
case 2:
{
lean_object* v_err_312_; lean_object* v___y_314_; lean_object* v___x_323_; uint8_t v___x_324_; 
v_err_312_ = lean_ctor_get(v_x_244_, 0);
lean_inc(v_err_312_);
lean_dec_ref(v_x_244_);
v___x_323_ = lean_unsigned_to_nat(1024u);
v___x_324_ = lean_nat_dec_le(v___x_323_, v_prec_245_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; 
v___x_325_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13);
v___y_314_ = v___x_325_;
goto v___jp_313_;
}
else
{
lean_object* v___x_326_; 
v___x_326_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14);
v___y_314_ = v___x_326_;
goto v___jp_313_;
}
v___jp_313_:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_315_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__20));
v___x_316_ = lean_unsigned_to_nat(1024u);
v___x_317_ = l_Std_Http_Protocol_H1_instReprError_repr(v_err_312_, v___x_316_);
v___x_318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_315_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
lean_inc(v___y_314_);
v___x_319_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_319_, 0, v___y_314_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = 0;
v___x_321_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_321_, 0, v___x_319_);
lean_ctor_set_uint8(v___x_321_, sizeof(void*)*1, v___x_320_);
v___x_322_ = l_Repr_addAppParen(v___x_321_, v_prec_245_);
return v___x_322_;
}
}
case 3:
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = lean_unsigned_to_nat(1024u);
v___x_328_ = lean_nat_dec_le(v___x_327_, v_prec_245_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; 
v___x_329_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13);
v___y_247_ = v___x_329_;
goto v___jp_246_;
}
else
{
lean_object* v___x_330_; 
v___x_330_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14);
v___y_247_ = v___x_330_;
goto v___jp_246_;
}
}
case 4:
{
lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = lean_unsigned_to_nat(1024u);
v___x_332_ = lean_nat_dec_le(v___x_331_, v_prec_245_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
v___x_333_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13);
v___y_254_ = v___x_333_;
goto v___jp_253_;
}
else
{
lean_object* v___x_334_; 
v___x_334_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14);
v___y_254_ = v___x_334_;
goto v___jp_253_;
}
}
case 5:
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = lean_unsigned_to_nat(1024u);
v___x_336_ = lean_nat_dec_le(v___x_335_, v_prec_245_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; 
v___x_337_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13);
v___y_261_ = v___x_337_;
goto v___jp_260_;
}
else
{
lean_object* v___x_338_; 
v___x_338_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14);
v___y_261_ = v___x_338_;
goto v___jp_260_;
}
}
case 6:
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = lean_unsigned_to_nat(1024u);
v___x_340_ = lean_nat_dec_le(v___x_339_, v_prec_245_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; 
v___x_341_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13);
v___y_268_ = v___x_341_;
goto v___jp_267_;
}
else
{
lean_object* v___x_342_; 
v___x_342_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14);
v___y_268_ = v___x_342_;
goto v___jp_267_;
}
}
default: 
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = lean_unsigned_to_nat(1024u);
v___x_344_ = lean_nat_dec_le(v___x_343_, v_prec_245_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; 
v___x_345_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13);
v___y_275_ = v___x_345_;
goto v___jp_274_;
}
else
{
lean_object* v___x_346_; 
v___x_346_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14);
v___y_275_ = v___x_346_;
goto v___jp_274_;
}
}
}
v___jp_246_:
{
lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_248_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__1));
lean_inc(v___y_247_);
v___x_249_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_249_, 0, v___y_247_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = 0;
v___x_251_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_251_, 0, v___x_249_);
lean_ctor_set_uint8(v___x_251_, sizeof(void*)*1, v___x_250_);
v___x_252_ = l_Repr_addAppParen(v___x_251_, v_prec_245_);
return v___x_252_;
}
v___jp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_255_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__3));
lean_inc(v___y_254_);
v___x_256_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_256_, 0, v___y_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = 0;
v___x_258_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_258_, 0, v___x_256_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*1, v___x_257_);
v___x_259_ = l_Repr_addAppParen(v___x_258_, v_prec_245_);
return v___x_259_;
}
v___jp_260_:
{
lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_262_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__5));
lean_inc(v___y_261_);
v___x_263_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_263_, 0, v___y_261_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = 0;
v___x_265_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*1, v___x_264_);
v___x_266_ = l_Repr_addAppParen(v___x_265_, v_prec_245_);
return v___x_266_;
}
v___jp_267_:
{
lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_269_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__7));
lean_inc(v___y_268_);
v___x_270_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_270_, 0, v___y_268_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = 0;
v___x_272_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set_uint8(v___x_272_, sizeof(void*)*1, v___x_271_);
v___x_273_ = l_Repr_addAppParen(v___x_272_, v_prec_245_);
return v___x_273_;
}
v___jp_274_:
{
lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_276_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__9));
lean_inc(v___y_275_);
v___x_277_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_277_, 0, v___y_275_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v___x_278_ = 0;
v___x_279_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_279_, 0, v___x_277_);
lean_ctor_set_uint8(v___x_279_, sizeof(void*)*1, v___x_278_);
v___x_280_ = l_Repr_addAppParen(v___x_279_, v_prec_245_);
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr___boxed(lean_object* v_dir_347_, lean_object* v_x_348_, lean_object* v_prec_349_){
_start:
{
uint8_t v_dir_701__boxed_350_; lean_object* v_res_351_; 
v_dir_701__boxed_350_ = lean_unbox(v_dir_347_);
v_res_351_ = l_Std_Http_Protocol_H1_instReprEvent_repr(v_dir_701__boxed_350_, v_x_348_, v_prec_349_);
lean_dec(v_prec_349_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprEvent(uint8_t v_dir_352_){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_box(v_dir_352_);
v___x_354_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_instReprEvent_repr___boxed), 3, 1);
lean_closure_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprEvent___boxed(lean_object* v_dir_355_){
_start:
{
uint8_t v_dir_5__boxed_356_; lean_object* v_res_357_; 
v_dir_5__boxed_356_ = lean_unbox(v_dir_355_);
v_res_357_ = l_Std_Http_Protocol_H1_instReprEvent(v_dir_5__boxed_356_);
return v_res_357_;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Internal(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Parser(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Config(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Message(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Error(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Protocol_H1_Event(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

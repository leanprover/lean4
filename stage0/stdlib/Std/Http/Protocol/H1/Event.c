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
lean_object* l_Std_Http_Protocol_H1_Event_ctorIdx___impl(uint8_t v_dir_5_, lean_object* v_x_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_tag_nat(v_x_6_);
return v___x_7_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Event_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_5_ = stack[0].m_num;
lean_object* v_x_6_ = stack[1].m_obj;
lean_object* v_res_8_;
v_res_8_ = l_Std_Http_Protocol_H1_Event_ctorIdx___impl(v_dir_5_, v_x_6_);
stack->m_obj
 = v_res_8_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorIdx___impl___boxed(lean_object* v_dir_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_dir_boxed_11_; lean_object* v_res_12_; 
v_dir_boxed_11_ = lean_unbox(v_dir_9_);
v_res_12_ = l_Std_Http_Protocol_H1_Event_ctorIdx___impl(v_dir_boxed_11_, v_x_10_);
lean_dec(v_x_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorElim___redArg(lean_object* v_t_13_, lean_object* v_k_14_){
_start:
{
switch(lean_obj_tag(v_t_13_))
{
case 0:
{
lean_object* v_head_15_; lean_object* v___x_16_; 
v_head_15_ = lean_ctor_get(v_t_13_, 0);
lean_inc(v_head_15_);
lean_dec_ref_known(v_t_13_, 1);
v___x_16_ = lean_apply_1(v_k_14_, v_head_15_);
return v___x_16_;
}
case 1:
{
lean_object* v_size_17_; lean_object* v___x_18_; 
v_size_17_ = lean_ctor_get(v_t_13_, 0);
lean_inc(v_size_17_);
lean_dec_ref_known(v_t_13_, 1);
v___x_18_ = lean_apply_1(v_k_14_, v_size_17_);
return v___x_18_;
}
case 2:
{
lean_object* v_err_19_; lean_object* v___x_20_; 
v_err_19_ = lean_ctor_get(v_t_13_, 0);
lean_inc(v_err_19_);
lean_dec_ref_known(v_t_13_, 1);
v___x_20_ = lean_apply_1(v_k_14_, v_err_19_);
return v___x_20_;
}
default: 
{
lean_dec(v_t_13_);
return v_k_14_;
}
}
}
}
lean_object* l_Std_Http_Protocol_H1_Event_ctorElim(uint8_t v_dir_21_, lean_object* v_motive_22_, lean_object* v_ctorIdx_23_, lean_object* v_t_24_, lean_object* v_h_25_, lean_object* v_k_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_24_, v_k_26_);
return v___x_27_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Event_ctorElim_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_21_ = stack[0].m_num;
lean_object* v_ctorIdx_23_ = stack[2].m_obj;
lean_object* v_t_24_ = stack[3].m_obj;
lean_object* v_k_26_ = stack[5].m_obj;
lean_object* v_res_28_;
v_res_28_ = l_Std_Http_Protocol_H1_Event_ctorElim(v_dir_21_, lean_box(0), v_ctorIdx_23_, v_t_24_, lean_box(0), v_k_26_);
stack->m_obj
 = v_res_28_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_ctorElim___boxed(lean_object* v_dir_29_, lean_object* v_motive_30_, lean_object* v_ctorIdx_31_, lean_object* v_t_32_, lean_object* v_h_33_, lean_object* v_k_34_){
_start:
{
uint8_t v_dir_boxed_35_; lean_object* v_res_36_; 
v_dir_boxed_35_ = lean_unbox(v_dir_29_);
v_res_36_ = l_Std_Http_Protocol_H1_Event_ctorElim(v_dir_boxed_35_, v_motive_30_, v_ctorIdx_31_, v_t_32_, v_h_33_, v_k_34_);
lean_dec(v_ctorIdx_31_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_endHeaders_elim___redArg(lean_object* v_t_37_, lean_object* v_endHeaders_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_37_, v_endHeaders_38_);
return v___x_39_;
}
}
lean_object* l_Std_Http_Protocol_H1_Event_endHeaders_elim(uint8_t v_dir_40_, lean_object* v_motive_41_, lean_object* v_t_42_, lean_object* v_h_43_, lean_object* v_endHeaders_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_42_, v_endHeaders_44_);
return v___x_45_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Event_endHeaders_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_40_ = stack[0].m_num;
lean_object* v_t_42_ = stack[2].m_obj;
lean_object* v_endHeaders_44_ = stack[4].m_obj;
lean_object* v_res_46_;
v_res_46_ = l_Std_Http_Protocol_H1_Event_endHeaders_elim(v_dir_40_, lean_box(0), v_t_42_, lean_box(0), v_endHeaders_44_);
stack->m_obj
 = v_res_46_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_endHeaders_elim___boxed(lean_object* v_dir_47_, lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_endHeaders_51_){
_start:
{
uint8_t v_dir_boxed_52_; lean_object* v_res_53_; 
v_dir_boxed_52_ = lean_unbox(v_dir_47_);
v_res_53_ = l_Std_Http_Protocol_H1_Event_endHeaders_elim(v_dir_boxed_52_, v_motive_48_, v_t_49_, v_h_50_, v_endHeaders_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_needMoreData_elim___redArg(lean_object* v_t_54_, lean_object* v_needMoreData_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_54_, v_needMoreData_55_);
return v___x_56_;
}
}
lean_object* l_Std_Http_Protocol_H1_Event_needMoreData_elim(uint8_t v_dir_57_, lean_object* v_motive_58_, lean_object* v_t_59_, lean_object* v_h_60_, lean_object* v_needMoreData_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_59_, v_needMoreData_61_);
return v___x_62_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Event_needMoreData_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_57_ = stack[0].m_num;
lean_object* v_t_59_ = stack[2].m_obj;
lean_object* v_needMoreData_61_ = stack[4].m_obj;
lean_object* v_res_63_;
v_res_63_ = l_Std_Http_Protocol_H1_Event_needMoreData_elim(v_dir_57_, lean_box(0), v_t_59_, lean_box(0), v_needMoreData_61_);
stack->m_obj
 = v_res_63_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_needMoreData_elim___boxed(lean_object* v_dir_64_, lean_object* v_motive_65_, lean_object* v_t_66_, lean_object* v_h_67_, lean_object* v_needMoreData_68_){
_start:
{
uint8_t v_dir_boxed_69_; lean_object* v_res_70_; 
v_dir_boxed_69_ = lean_unbox(v_dir_64_);
v_res_70_ = l_Std_Http_Protocol_H1_Event_needMoreData_elim(v_dir_boxed_69_, v_motive_65_, v_t_66_, v_h_67_, v_needMoreData_68_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_failed_elim___redArg(lean_object* v_t_71_, lean_object* v_failed_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_71_, v_failed_72_);
return v___x_73_;
}
}
lean_object* l_Std_Http_Protocol_H1_Event_failed_elim(uint8_t v_dir_74_, lean_object* v_motive_75_, lean_object* v_t_76_, lean_object* v_h_77_, lean_object* v_failed_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_76_, v_failed_78_);
return v___x_79_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Event_failed_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_74_ = stack[0].m_num;
lean_object* v_t_76_ = stack[2].m_obj;
lean_object* v_failed_78_ = stack[4].m_obj;
lean_object* v_res_80_;
v_res_80_ = l_Std_Http_Protocol_H1_Event_failed_elim(v_dir_74_, lean_box(0), v_t_76_, lean_box(0), v_failed_78_);
stack->m_obj
 = v_res_80_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_failed_elim___boxed(lean_object* v_dir_81_, lean_object* v_motive_82_, lean_object* v_t_83_, lean_object* v_h_84_, lean_object* v_failed_85_){
_start:
{
uint8_t v_dir_boxed_86_; lean_object* v_res_87_; 
v_dir_boxed_86_ = lean_unbox(v_dir_81_);
v_res_87_ = l_Std_Http_Protocol_H1_Event_failed_elim(v_dir_boxed_86_, v_motive_82_, v_t_83_, v_h_84_, v_failed_85_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_close_elim___redArg(lean_object* v_t_88_, lean_object* v_close_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_88_, v_close_89_);
return v___x_90_;
}
}
lean_object* l_Std_Http_Protocol_H1_Event_close_elim(uint8_t v_dir_91_, lean_object* v_motive_92_, lean_object* v_t_93_, lean_object* v_h_94_, lean_object* v_close_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_93_, v_close_95_);
return v___x_96_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Event_close_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_91_ = stack[0].m_num;
lean_object* v_t_93_ = stack[2].m_obj;
lean_object* v_close_95_ = stack[4].m_obj;
lean_object* v_res_97_;
v_res_97_ = l_Std_Http_Protocol_H1_Event_close_elim(v_dir_91_, lean_box(0), v_t_93_, lean_box(0), v_close_95_);
stack->m_obj
 = v_res_97_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_close_elim___boxed(lean_object* v_dir_98_, lean_object* v_motive_99_, lean_object* v_t_100_, lean_object* v_h_101_, lean_object* v_close_102_){
_start:
{
uint8_t v_dir_boxed_103_; lean_object* v_res_104_; 
v_dir_boxed_103_ = lean_unbox(v_dir_98_);
v_res_104_ = l_Std_Http_Protocol_H1_Event_close_elim(v_dir_boxed_103_, v_motive_99_, v_t_100_, v_h_101_, v_close_102_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_closeBody_elim___redArg(lean_object* v_t_105_, lean_object* v_closeBody_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_105_, v_closeBody_106_);
return v___x_107_;
}
}
lean_object* l_Std_Http_Protocol_H1_Event_closeBody_elim(uint8_t v_dir_108_, lean_object* v_motive_109_, lean_object* v_t_110_, lean_object* v_h_111_, lean_object* v_closeBody_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_110_, v_closeBody_112_);
return v___x_113_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Event_closeBody_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_108_ = stack[0].m_num;
lean_object* v_t_110_ = stack[2].m_obj;
lean_object* v_closeBody_112_ = stack[4].m_obj;
lean_object* v_res_114_;
v_res_114_ = l_Std_Http_Protocol_H1_Event_closeBody_elim(v_dir_108_, lean_box(0), v_t_110_, lean_box(0), v_closeBody_112_);
stack->m_obj
 = v_res_114_;
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
lean_object* l_Std_Http_Protocol_H1_Event_needAnswer_elim(uint8_t v_dir_125_, lean_object* v_motive_126_, lean_object* v_t_127_, lean_object* v_h_128_, lean_object* v_needAnswer_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_127_, v_needAnswer_129_);
return v___x_130_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Event_needAnswer_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_125_ = stack[0].m_num;
lean_object* v_t_127_ = stack[2].m_obj;
lean_object* v_needAnswer_129_ = stack[4].m_obj;
lean_object* v_res_131_;
v_res_131_ = l_Std_Http_Protocol_H1_Event_needAnswer_elim(v_dir_125_, lean_box(0), v_t_127_, lean_box(0), v_needAnswer_129_);
stack->m_obj
 = v_res_131_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_needAnswer_elim___boxed(lean_object* v_dir_132_, lean_object* v_motive_133_, lean_object* v_t_134_, lean_object* v_h_135_, lean_object* v_needAnswer_136_){
_start:
{
uint8_t v_dir_boxed_137_; lean_object* v_res_138_; 
v_dir_boxed_137_ = lean_unbox(v_dir_132_);
v_res_138_ = l_Std_Http_Protocol_H1_Event_needAnswer_elim(v_dir_boxed_137_, v_motive_133_, v_t_134_, v_h_135_, v_needAnswer_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_next_elim___redArg(lean_object* v_t_139_, lean_object* v_next_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_139_, v_next_140_);
return v___x_141_;
}
}
lean_object* l_Std_Http_Protocol_H1_Event_next_elim(uint8_t v_dir_142_, lean_object* v_motive_143_, lean_object* v_t_144_, lean_object* v_h_145_, lean_object* v_next_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_144_, v_next_146_);
return v___x_147_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Event_next_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_142_ = stack[0].m_num;
lean_object* v_t_144_ = stack[2].m_obj;
lean_object* v_next_146_ = stack[4].m_obj;
lean_object* v_res_148_;
v_res_148_ = l_Std_Http_Protocol_H1_Event_next_elim(v_dir_142_, lean_box(0), v_t_144_, lean_box(0), v_next_146_);
stack->m_obj
 = v_res_148_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_next_elim___boxed(lean_object* v_dir_149_, lean_object* v_motive_150_, lean_object* v_t_151_, lean_object* v_h_152_, lean_object* v_next_153_){
_start:
{
uint8_t v_dir_boxed_154_; lean_object* v_res_155_; 
v_dir_boxed_154_ = lean_unbox(v_dir_149_);
v_res_155_ = l_Std_Http_Protocol_H1_Event_next_elim(v_dir_boxed_154_, v_motive_150_, v_t_151_, v_h_152_, v_next_153_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_continue_elim___redArg(lean_object* v_t_156_, lean_object* v_continue_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_156_, v_continue_157_);
return v___x_158_;
}
}
lean_object* l_Std_Http_Protocol_H1_Event_continue_elim(uint8_t v_dir_159_, lean_object* v_motive_160_, lean_object* v_t_161_, lean_object* v_h_162_, lean_object* v_continue_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_161_, v_continue_163_);
return v___x_164_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Event_continue_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_159_ = stack[0].m_num;
lean_object* v_t_161_ = stack[2].m_obj;
lean_object* v_continue_163_ = stack[4].m_obj;
lean_object* v_res_165_;
v_res_165_ = l_Std_Http_Protocol_H1_Event_continue_elim(v_dir_159_, lean_box(0), v_t_161_, lean_box(0), v_continue_163_);
stack->m_obj
 = v_res_165_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Event_continue_elim___boxed(lean_object* v_dir_166_, lean_object* v_motive_167_, lean_object* v_t_168_, lean_object* v_h_169_, lean_object* v_continue_170_){
_start:
{
uint8_t v_dir_boxed_171_; lean_object* v_res_172_; 
v_dir_boxed_171_ = lean_unbox(v_dir_166_);
v_res_172_ = l_Std_Http_Protocol_H1_Event_continue_elim(v_dir_boxed_171_, v_motive_167_, v_t_168_, v_h_169_, v_continue_170_);
return v_res_172_;
}
}
lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent_default___redArg(){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = ((lean_object*)(l_Std_Http_Protocol_H1_instInhabitedEvent_default___redArg___closed__0));
return v___x_176_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_instInhabitedEvent_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_177_;
v_res_177_ = l_Std_Http_Protocol_H1_instInhabitedEvent_default___redArg();
stack->m_obj
 = v_res_177_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent_default___redArg___boxed(lean_object* v___dummy_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Std_Http_Protocol_H1_instInhabitedEvent_default___redArg();
return v_res_179_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0(void){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Std_Http_Protocol_H1_instInhabitedEvent_default___redArg();
return v___x_180_;
}
}
lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent_default(uint8_t v_dir_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lean_obj_once(&l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0, &l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0_once, _init_l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0);
return v___x_182_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_instInhabitedEvent_default_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_181_ = stack[0].m_num;
lean_object* v_res_183_;
v_res_183_ = l_Std_Http_Protocol_H1_instInhabitedEvent_default(v_dir_181_);
stack->m_obj
 = v_res_183_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent_default___boxed(lean_object* v_dir_184_){
_start:
{
uint8_t v_dir_boxed_185_; lean_object* v_res_186_; 
v_dir_boxed_185_ = lean_unbox(v_dir_184_);
v_res_186_ = l_Std_Http_Protocol_H1_instInhabitedEvent_default(v_dir_boxed_185_);
return v_res_186_;
}
}
lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent___redArg(){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = lean_obj_once(&l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0, &l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0_once, _init_l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0);
return v___x_188_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_instInhabitedEvent___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_189_;
v_res_189_ = l_Std_Http_Protocol_H1_instInhabitedEvent___redArg();
stack->m_obj
 = v_res_189_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent___redArg___boxed(lean_object* v___dummy_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Std_Http_Protocol_H1_instInhabitedEvent___redArg();
return v_res_191_;
}
}
lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent(uint8_t v_a_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = lean_obj_once(&l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0, &l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0_once, _init_l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0);
return v___x_193_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_instInhabitedEvent_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_192_ = stack[0].m_num;
lean_object* v_res_194_;
v_res_194_ = l_Std_Http_Protocol_H1_instInhabitedEvent(v_a_192_);
stack->m_obj
 = v_res_194_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedEvent___boxed(lean_object* v_a_195_){
_start:
{
uint8_t v_a_14__boxed_196_; lean_object* v_res_197_; 
v_a_14__boxed_196_ = lean_unbox(v_a_195_);
v_res_197_ = l_Std_Http_Protocol_H1_instInhabitedEvent(v_a_14__boxed_196_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0(lean_object* v_x_204_, lean_object* v_x_205_){
_start:
{
if (lean_obj_tag(v_x_204_) == 0)
{
lean_object* v___x_206_; 
v___x_206_ = ((lean_object*)(l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__1));
return v___x_206_;
}
else
{
lean_object* v_val_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_218_; 
v_val_207_ = lean_ctor_get(v_x_204_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v_x_204_);
if (v_isSharedCheck_218_ == 0)
{
v___x_209_ = v_x_204_;
v_isShared_210_ = v_isSharedCheck_218_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_val_207_);
lean_dec(v_x_204_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_218_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_214_; 
v___x_211_ = ((lean_object*)(l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__3));
v___x_212_ = l_Nat_reprFast(v_val_207_);
if (v_isShared_210_ == 0)
{
lean_ctor_set_tag(v___x_209_, 3);
lean_ctor_set(v___x_209_, 0, v___x_212_);
v___x_214_ = v___x_209_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_212_);
v___x_214_ = v_reuseFailAlloc_217_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_211_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
v___x_216_ = l_Repr_addAppParen(v___x_215_, v_x_205_);
return v___x_216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___boxed(lean_object* v_x_219_, lean_object* v_x_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0(v_x_219_, v_x_220_);
lean_dec(v_x_220_);
return v_res_221_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_unsigned_to_nat(2u);
v___x_244_ = lean_nat_to_int(v___x_243_);
return v___x_244_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_unsigned_to_nat(1u);
v___x_246_ = lean_nat_to_int(v___x_245_);
return v___x_246_;
}
}
lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr(uint8_t v_dir_259_, lean_object* v_x_260_, lean_object* v_prec_261_){
_start:
{
lean_object* v___y_263_; lean_object* v___y_270_; lean_object* v___y_277_; lean_object* v___y_284_; lean_object* v___y_291_; 
switch(lean_obj_tag(v_x_260_))
{
case 0:
{
lean_object* v_head_297_; lean_object* v___y_299_; lean_object* v___x_309_; uint8_t v___x_310_; 
v_head_297_ = lean_ctor_get(v_x_260_, 0);
lean_inc(v_head_297_);
lean_dec_ref_known(v_x_260_, 1);
v___x_309_ = lean_unsigned_to_nat(1024u);
v___x_310_ = lean_nat_dec_le(v___x_309_, v_prec_261_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; 
v___x_311_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13);
v___y_299_ = v___x_311_;
goto v___jp_298_;
}
else
{
lean_object* v___x_312_; 
v___x_312_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14);
v___y_299_ = v___x_312_;
goto v___jp_298_;
}
v___jp_298_:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_351__overap_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_300_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__12));
v___x_301_ = lean_unsigned_to_nat(1024u);
v___x_351__overap_302_ = l_Std_Http_Protocol_H1_instReprHead(v_dir_259_);
v___x_303_ = lean_apply_2(v___x_351__overap_302_, v_head_297_, v___x_301_);
v___x_304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_300_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
lean_inc(v___y_299_);
v___x_305_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_305_, 0, v___y_299_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = 0;
v___x_307_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_307_, 0, v___x_305_);
lean_ctor_set_uint8(v___x_307_, sizeof(void*)*1, v___x_306_);
v___x_308_ = l_Repr_addAppParen(v___x_307_, v_prec_261_);
return v___x_308_;
}
}
case 1:
{
lean_object* v_size_313_; lean_object* v___y_315_; lean_object* v___x_324_; uint8_t v___x_325_; 
v_size_313_ = lean_ctor_get(v_x_260_, 0);
lean_inc(v_size_313_);
lean_dec_ref_known(v_x_260_, 1);
v___x_324_ = lean_unsigned_to_nat(1024u);
v___x_325_ = lean_nat_dec_le(v___x_324_, v_prec_261_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
v___x_326_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13);
v___y_315_ = v___x_326_;
goto v___jp_314_;
}
else
{
lean_object* v___x_327_; 
v___x_327_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14);
v___y_315_ = v___x_327_;
goto v___jp_314_;
}
v___jp_314_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_316_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__17));
v___x_317_ = lean_unsigned_to_nat(1024u);
v___x_318_ = l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0(v_size_313_, v___x_317_);
v___x_319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_316_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
lean_inc(v___y_315_);
v___x_320_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_320_, 0, v___y_315_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = 0;
v___x_322_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_322_, 0, v___x_320_);
lean_ctor_set_uint8(v___x_322_, sizeof(void*)*1, v___x_321_);
v___x_323_ = l_Repr_addAppParen(v___x_322_, v_prec_261_);
return v___x_323_;
}
}
case 2:
{
lean_object* v_err_328_; lean_object* v___y_330_; lean_object* v___x_339_; uint8_t v___x_340_; 
v_err_328_ = lean_ctor_get(v_x_260_, 0);
lean_inc(v_err_328_);
lean_dec_ref_known(v_x_260_, 1);
v___x_339_ = lean_unsigned_to_nat(1024u);
v___x_340_ = lean_nat_dec_le(v___x_339_, v_prec_261_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; 
v___x_341_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13);
v___y_330_ = v___x_341_;
goto v___jp_329_;
}
else
{
lean_object* v___x_342_; 
v___x_342_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14);
v___y_330_ = v___x_342_;
goto v___jp_329_;
}
v___jp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_331_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__20));
v___x_332_ = lean_unsigned_to_nat(1024u);
v___x_333_ = l_Std_Http_Protocol_H1_instReprError_repr(v_err_328_, v___x_332_);
v___x_334_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_331_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
lean_inc(v___y_330_);
v___x_335_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_335_, 0, v___y_330_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = 0;
v___x_337_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_337_, 0, v___x_335_);
lean_ctor_set_uint8(v___x_337_, sizeof(void*)*1, v___x_336_);
v___x_338_ = l_Repr_addAppParen(v___x_337_, v_prec_261_);
return v___x_338_;
}
}
case 3:
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = lean_unsigned_to_nat(1024u);
v___x_344_ = lean_nat_dec_le(v___x_343_, v_prec_261_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; 
v___x_345_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13);
v___y_263_ = v___x_345_;
goto v___jp_262_;
}
else
{
lean_object* v___x_346_; 
v___x_346_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14);
v___y_263_ = v___x_346_;
goto v___jp_262_;
}
}
case 4:
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = lean_unsigned_to_nat(1024u);
v___x_348_ = lean_nat_dec_le(v___x_347_, v_prec_261_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; 
v___x_349_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13);
v___y_270_ = v___x_349_;
goto v___jp_269_;
}
else
{
lean_object* v___x_350_; 
v___x_350_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14);
v___y_270_ = v___x_350_;
goto v___jp_269_;
}
}
case 5:
{
lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_351_ = lean_unsigned_to_nat(1024u);
v___x_352_ = lean_nat_dec_le(v___x_351_, v_prec_261_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; 
v___x_353_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13);
v___y_277_ = v___x_353_;
goto v___jp_276_;
}
else
{
lean_object* v___x_354_; 
v___x_354_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14);
v___y_277_ = v___x_354_;
goto v___jp_276_;
}
}
case 6:
{
lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_355_ = lean_unsigned_to_nat(1024u);
v___x_356_ = lean_nat_dec_le(v___x_355_, v_prec_261_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; 
v___x_357_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13);
v___y_284_ = v___x_357_;
goto v___jp_283_;
}
else
{
lean_object* v___x_358_; 
v___x_358_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14);
v___y_284_ = v___x_358_;
goto v___jp_283_;
}
}
default: 
{
lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_359_ = lean_unsigned_to_nat(1024u);
v___x_360_ = lean_nat_dec_le(v___x_359_, v_prec_261_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; 
v___x_361_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13);
v___y_291_ = v___x_361_;
goto v___jp_290_;
}
else
{
lean_object* v___x_362_; 
v___x_362_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14, &l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once, _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14);
v___y_291_ = v___x_362_;
goto v___jp_290_;
}
}
}
v___jp_262_:
{
lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_264_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__1));
lean_inc(v___y_263_);
v___x_265_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_265_, 0, v___y_263_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = 0;
v___x_267_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_267_, 0, v___x_265_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*1, v___x_266_);
v___x_268_ = l_Repr_addAppParen(v___x_267_, v_prec_261_);
return v___x_268_;
}
v___jp_269_:
{
lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_271_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__3));
lean_inc(v___y_270_);
v___x_272_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_272_, 0, v___y_270_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = 0;
v___x_274_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_274_, 0, v___x_272_);
lean_ctor_set_uint8(v___x_274_, sizeof(void*)*1, v___x_273_);
v___x_275_ = l_Repr_addAppParen(v___x_274_, v_prec_261_);
return v___x_275_;
}
v___jp_276_:
{
lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_278_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__5));
lean_inc(v___y_277_);
v___x_279_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_279_, 0, v___y_277_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v___x_280_ = 0;
v___x_281_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_281_, 0, v___x_279_);
lean_ctor_set_uint8(v___x_281_, sizeof(void*)*1, v___x_280_);
v___x_282_ = l_Repr_addAppParen(v___x_281_, v_prec_261_);
return v___x_282_;
}
v___jp_283_:
{
lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_285_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__7));
lean_inc(v___y_284_);
v___x_286_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_286_, 0, v___y_284_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = 0;
v___x_288_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set_uint8(v___x_288_, sizeof(void*)*1, v___x_287_);
v___x_289_ = l_Repr_addAppParen(v___x_288_, v_prec_261_);
return v___x_289_;
}
v___jp_290_:
{
lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_292_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__9));
lean_inc(v___y_291_);
v___x_293_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_293_, 0, v___y_291_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = 0;
v___x_295_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_295_, 0, v___x_293_);
lean_ctor_set_uint8(v___x_295_, sizeof(void*)*1, v___x_294_);
v___x_296_ = l_Repr_addAppParen(v___x_295_, v_prec_261_);
return v___x_296_;
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_instReprEvent_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_259_ = stack[0].m_num;
lean_object* v_x_260_ = stack[1].m_obj;
lean_object* v_prec_261_ = stack[2].m_obj;
lean_object* v_res_363_;
v_res_363_ = l_Std_Http_Protocol_H1_instReprEvent_repr(v_dir_259_, v_x_260_, v_prec_261_);
stack->m_obj
 = v_res_363_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprEvent_repr___boxed(lean_object* v_dir_364_, lean_object* v_x_365_, lean_object* v_prec_366_){
_start:
{
uint8_t v_dir_708__boxed_367_; lean_object* v_res_368_; 
v_dir_708__boxed_367_ = lean_unbox(v_dir_364_);
v_res_368_ = l_Std_Http_Protocol_H1_instReprEvent_repr(v_dir_708__boxed_367_, v_x_365_, v_prec_366_);
lean_dec(v_prec_366_);
return v_res_368_;
}
}
lean_object* l_Std_Http_Protocol_H1_instReprEvent(uint8_t v_dir_369_){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_box(v_dir_369_);
v___x_371_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_instReprEvent_repr___boxed), 3, 1);
lean_closure_set(v___x_371_, 0, v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_instReprEvent_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_369_ = stack[0].m_num;
lean_object* v_res_372_;
v_res_372_ = l_Std_Http_Protocol_H1_instReprEvent(v_dir_369_);
stack->m_obj
 = v_res_372_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprEvent___boxed(lean_object* v_dir_373_){
_start:
{
uint8_t v_dir_5__boxed_374_; lean_object* v_res_375_; 
v_dir_5__boxed_374_ = lean_unbox(v_dir_373_);
v_res_375_ = l_Std_Http_Protocol_H1_instReprEvent(v_dir_5__boxed_374_);
return v_res_375_;
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

// Lean compiler output
// Module: Lean.Elab.Time
// Imports: public import Lean.Elab.Command
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
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* lean_io_mono_ms_now();
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Time_elabTimeCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__0 = (const lean_object*)&l_Lean_Elab_Time_elabTimeCmd___closed__0_value;
static const lean_string_object l_Lean_Elab_Time_elabTimeCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__1 = (const lean_object*)&l_Lean_Elab_Time_elabTimeCmd___closed__1_value;
static const lean_string_object l_Lean_Elab_Time_elabTimeCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "timeCmd"};
static const lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__2 = (const lean_object*)&l_Lean_Elab_Time_elabTimeCmd___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Time_elabTimeCmd___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Time_elabTimeCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Time_elabTimeCmd___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Time_elabTimeCmd___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Time_elabTimeCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Time_elabTimeCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Time_elabTimeCmd___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Time_elabTimeCmd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(241, 30, 11, 88, 214, 137, 225, 32)}};
static const lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__3 = (const lean_object*)&l_Lean_Elab_Time_elabTimeCmd___closed__3_value;
static const lean_string_object l_Lean_Elab_Time_elabTimeCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "time: "};
static const lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__4 = (const lean_object*)&l_Lean_Elab_Time_elabTimeCmd___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Time_elabTimeCmd___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__5;
static const lean_string_object l_Lean_Elab_Time_elabTimeCmd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ms"};
static const lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__6 = (const lean_object*)&l_Lean_Elab_Time_elabTimeCmd___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Time_elabTimeCmd___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Time_elabTimeCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Time_elabTimeCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Time"};
static const lean_object* l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "elabTimeCmd"};
static const lean_object* l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Time_elabTimeCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 109, 103, 22, 229, 14, 107, 103)}};
static const lean_ctor_object l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(76, 103, 203, 174, 210, 209, 148, 47)}};
static const lean_object* l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0(lean_object* v_00_u03b1_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg();
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___boxed(lean_object* v_00_u03b1_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0(v_00_u03b1_14_, v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
return v_res_18_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0(uint8_t v_suppressElabErrors_20_, uint8_t v___y_21_, lean_object* v_x_22_){
_start:
{
if (lean_obj_tag(v_x_22_) == 1)
{
lean_object* v_pre_23_; 
v_pre_23_ = lean_ctor_get(v_x_22_, 0);
if (lean_obj_tag(v_pre_23_) == 0)
{
lean_object* v_str_24_; lean_object* v___x_25_; uint8_t v___x_26_; 
v_str_24_ = lean_ctor_get(v_x_22_, 1);
v___x_25_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0___closed__0));
v___x_26_ = lean_string_dec_eq(v_str_24_, v___x_25_);
if (v___x_26_ == 0)
{
return v___x_26_;
}
else
{
return v_suppressElabErrors_20_;
}
}
else
{
return v___y_21_;
}
}
else
{
return v___y_21_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_27_, lean_object* v___y_28_, lean_object* v_x_29_){
_start:
{
uint8_t v_suppressElabErrors_boxed_30_; uint8_t v___y_2707__boxed_31_; uint8_t v_res_32_; lean_object* v_r_33_; 
v_suppressElabErrors_boxed_30_ = lean_unbox(v_suppressElabErrors_27_);
v___y_2707__boxed_31_ = lean_unbox(v___y_28_);
v_res_32_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0(v_suppressElabErrors_boxed_30_, v___y_2707__boxed_31_, v_x_29_);
lean_dec(v_x_29_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__3(lean_object* v_opts_34_, lean_object* v_opt_35_){
_start:
{
lean_object* v_name_36_; lean_object* v_defValue_37_; lean_object* v_map_38_; lean_object* v___x_39_; 
v_name_36_ = lean_ctor_get(v_opt_35_, 0);
v_defValue_37_ = lean_ctor_get(v_opt_35_, 1);
v_map_38_ = lean_ctor_get(v_opts_34_, 0);
v___x_39_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_38_, v_name_36_);
if (lean_obj_tag(v___x_39_) == 0)
{
uint8_t v___x_40_; 
v___x_40_ = lean_unbox(v_defValue_37_);
return v___x_40_;
}
else
{
lean_object* v_val_41_; 
v_val_41_ = lean_ctor_get(v___x_39_, 0);
lean_inc(v_val_41_);
lean_dec_ref_known(v___x_39_, 1);
if (lean_obj_tag(v_val_41_) == 1)
{
uint8_t v_v_42_; 
v_v_42_ = lean_ctor_get_uint8(v_val_41_, 0);
lean_dec_ref_known(v_val_41_, 0);
return v_v_42_;
}
else
{
uint8_t v___x_43_; 
lean_dec(v_val_41_);
v___x_43_ = lean_unbox(v_defValue_37_);
return v___x_43_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__3___boxed(lean_object* v_opts_44_, lean_object* v_opt_45_){
_start:
{
uint8_t v_res_46_; lean_object* v_r_47_; 
v_res_46_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__3(v_opts_44_, v_opt_45_);
lean_dec_ref(v_opt_45_);
lean_dec_ref(v_opts_44_);
v_r_47_ = lean_box(v_res_46_);
return v_r_47_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_48_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_50_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_52_ = lean_unsigned_to_nat(0u);
v___x_53_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v___x_52_);
lean_ctor_set(v___x_53_, 2, v___x_52_);
lean_ctor_set(v___x_53_, 3, v___x_52_);
lean_ctor_set(v___x_53_, 4, v___x_51_);
lean_ctor_set(v___x_53_, 5, v___x_51_);
lean_ctor_set(v___x_53_, 6, v___x_51_);
lean_ctor_set(v___x_53_, 7, v___x_51_);
lean_ctor_set(v___x_53_, 8, v___x_51_);
lean_ctor_set(v___x_53_, 9, v___x_51_);
lean_ctor_set(v___x_53_, 10, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_unsigned_to_nat(32u);
v___x_55_ = lean_mk_empty_array_with_capacity(v___x_54_);
v___x_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_57_ = ((size_t)5ULL);
v___x_58_ = lean_unsigned_to_nat(0u);
v___x_59_ = lean_unsigned_to_nat(32u);
v___x_60_ = lean_mk_empty_array_with_capacity(v___x_59_);
v___x_61_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3);
v___x_62_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
lean_ctor_set(v___x_62_, 2, v___x_58_);
lean_ctor_set(v___x_62_, 3, v___x_58_);
lean_ctor_set_usize(v___x_62_, 4, v___x_57_);
return v___x_62_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_63_ = lean_box(1);
v___x_64_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4);
v___x_65_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_66_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v___x_64_);
lean_ctor_set(v___x_66_, 2, v___x_63_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg(lean_object* v_msgData_67_, lean_object* v___y_68_){
_start:
{
lean_object* v___x_70_; lean_object* v_env_71_; lean_object* v___x_72_; lean_object* v_scopes_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v_opts_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_70_ = lean_st_ref_get(v___y_68_);
v_env_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc_ref(v_env_71_);
lean_dec(v___x_70_);
v___x_72_ = lean_st_ref_get(v___y_68_);
v_scopes_73_ = lean_ctor_get(v___x_72_, 2);
lean_inc(v_scopes_73_);
lean_dec(v___x_72_);
v___x_74_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_75_ = l_List_head_x21___redArg(v___x_74_, v_scopes_73_);
lean_dec(v_scopes_73_);
v_opts_76_ = lean_ctor_get(v___x_75_, 1);
lean_inc_ref(v_opts_76_);
lean_dec(v___x_75_);
v___x_77_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_78_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5);
v___x_79_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_79_, 0, v_env_71_);
lean_ctor_set(v___x_79_, 1, v___x_77_);
lean_ctor_set(v___x_79_, 2, v___x_78_);
lean_ctor_set(v___x_79_, 3, v_opts_76_);
v___x_80_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v_msgData_67_);
v___x_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg(v_msgData_82_, v___y_83_);
lean_dec(v___y_83_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1(lean_object* v_ref_87_, lean_object* v_msgData_88_, uint8_t v_severity_89_, uint8_t v_isSilent_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v___y_95_; lean_object* v___y_96_; lean_object* v___y_97_; lean_object* v___y_98_; uint8_t v___y_99_; uint8_t v___y_100_; lean_object* v___y_101_; lean_object* v___y_102_; uint8_t v___y_160_; lean_object* v___y_161_; uint8_t v___y_162_; uint8_t v___y_163_; lean_object* v___y_164_; uint8_t v___y_188_; lean_object* v___y_189_; uint8_t v___y_190_; uint8_t v___y_191_; lean_object* v___y_192_; uint8_t v___y_196_; uint8_t v___y_197_; uint8_t v___y_198_; uint8_t v___x_213_; uint8_t v___y_215_; uint8_t v___y_216_; uint8_t v___y_217_; uint8_t v___y_219_; uint8_t v___x_231_; 
v___x_213_ = 2;
v___x_231_ = l_Lean_instBEqMessageSeverity_beq(v_severity_89_, v___x_213_);
if (v___x_231_ == 0)
{
v___y_219_ = v___x_231_;
goto v___jp_218_;
}
else
{
uint8_t v___x_232_; 
lean_inc_ref(v_msgData_88_);
v___x_232_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_88_);
v___y_219_ = v___x_232_;
goto v___jp_218_;
}
v___jp_94_:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_Elab_Command_getScope___redArg(v___y_102_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v_a_104_; lean_object* v___x_105_; 
v_a_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_a_104_);
lean_dec_ref_known(v___x_103_, 1);
v___x_105_ = l_Lean_Elab_Command_getScope___redArg(v___y_102_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_142_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_142_ == 0)
{
v___x_108_ = v___x_105_;
v_isShared_109_ = v_isSharedCheck_142_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_105_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_142_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_110_; lean_object* v_currNamespace_111_; lean_object* v_openDecls_112_; lean_object* v_env_113_; lean_object* v_messages_114_; lean_object* v_scopes_115_; lean_object* v_usedQuotCtxts_116_; lean_object* v_nextMacroScope_117_; lean_object* v_maxRecDepth_118_; lean_object* v_ngen_119_; lean_object* v_auxDeclNGen_120_; lean_object* v_infoState_121_; lean_object* v_traceState_122_; lean_object* v_snapshotTasks_123_; lean_object* v_prevLinterStates_124_; lean_object* v_codeQualityEntryTasks_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_141_; 
v___x_110_ = lean_st_ref_take(v___y_102_);
v_currNamespace_111_ = lean_ctor_get(v_a_104_, 2);
lean_inc(v_currNamespace_111_);
lean_dec(v_a_104_);
v_openDecls_112_ = lean_ctor_get(v_a_106_, 3);
lean_inc(v_openDecls_112_);
lean_dec(v_a_106_);
v_env_113_ = lean_ctor_get(v___x_110_, 0);
v_messages_114_ = lean_ctor_get(v___x_110_, 1);
v_scopes_115_ = lean_ctor_get(v___x_110_, 2);
v_usedQuotCtxts_116_ = lean_ctor_get(v___x_110_, 3);
v_nextMacroScope_117_ = lean_ctor_get(v___x_110_, 4);
v_maxRecDepth_118_ = lean_ctor_get(v___x_110_, 5);
v_ngen_119_ = lean_ctor_get(v___x_110_, 6);
v_auxDeclNGen_120_ = lean_ctor_get(v___x_110_, 7);
v_infoState_121_ = lean_ctor_get(v___x_110_, 8);
v_traceState_122_ = lean_ctor_get(v___x_110_, 9);
v_snapshotTasks_123_ = lean_ctor_get(v___x_110_, 10);
v_prevLinterStates_124_ = lean_ctor_get(v___x_110_, 11);
v_codeQualityEntryTasks_125_ = lean_ctor_get(v___x_110_, 12);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_141_ == 0)
{
v___x_127_ = v___x_110_;
v_isShared_128_ = v_isSharedCheck_141_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_codeQualityEntryTasks_125_);
lean_inc(v_prevLinterStates_124_);
lean_inc(v_snapshotTasks_123_);
lean_inc(v_traceState_122_);
lean_inc(v_infoState_121_);
lean_inc(v_auxDeclNGen_120_);
lean_inc(v_ngen_119_);
lean_inc(v_maxRecDepth_118_);
lean_inc(v_nextMacroScope_117_);
lean_inc(v_usedQuotCtxts_116_);
lean_inc(v_scopes_115_);
lean_inc(v_messages_114_);
lean_inc(v_env_113_);
lean_dec(v___x_110_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_141_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v_currNamespace_111_);
lean_ctor_set(v___x_129_, 1, v_openDecls_112_);
v___x_130_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v___y_96_);
lean_inc_ref(v___y_97_);
lean_inc_ref(v___y_101_);
v___x_131_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_131_, 0, v___y_101_);
lean_ctor_set(v___x_131_, 1, v___y_98_);
lean_ctor_set(v___x_131_, 2, v___y_95_);
lean_ctor_set(v___x_131_, 3, v___y_97_);
lean_ctor_set(v___x_131_, 4, v___x_130_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*5, v___y_99_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*5 + 1, v___y_100_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*5 + 2, v_isSilent_90_);
v___x_132_ = l_Lean_MessageLog_add(v___x_131_, v_messages_114_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v___x_132_);
v___x_134_ = v___x_127_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_env_113_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v___x_132_);
lean_ctor_set(v_reuseFailAlloc_140_, 2, v_scopes_115_);
lean_ctor_set(v_reuseFailAlloc_140_, 3, v_usedQuotCtxts_116_);
lean_ctor_set(v_reuseFailAlloc_140_, 4, v_nextMacroScope_117_);
lean_ctor_set(v_reuseFailAlloc_140_, 5, v_maxRecDepth_118_);
lean_ctor_set(v_reuseFailAlloc_140_, 6, v_ngen_119_);
lean_ctor_set(v_reuseFailAlloc_140_, 7, v_auxDeclNGen_120_);
lean_ctor_set(v_reuseFailAlloc_140_, 8, v_infoState_121_);
lean_ctor_set(v_reuseFailAlloc_140_, 9, v_traceState_122_);
lean_ctor_set(v_reuseFailAlloc_140_, 10, v_snapshotTasks_123_);
lean_ctor_set(v_reuseFailAlloc_140_, 11, v_prevLinterStates_124_);
lean_ctor_set(v_reuseFailAlloc_140_, 12, v_codeQualityEntryTasks_125_);
v___x_134_ = v_reuseFailAlloc_140_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_135_ = lean_st_ref_put(v___y_102_, v___x_134_);
v___x_136_ = lean_box(0);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 0, v___x_136_);
v___x_138_ = v___x_108_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
}
else
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
lean_dec(v_a_104_);
lean_dec_ref(v___y_98_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
v_a_143_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_150_ == 0)
{
v___x_145_ = v___x_105_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_105_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_143_);
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
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
lean_dec_ref(v___y_98_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
v_a_151_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v___x_103_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_103_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
v___jp_159_:
{
lean_object* v_fileName_165_; lean_object* v_fileMap_166_; uint8_t v_suppressElabErrors_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_186_; 
v_fileName_165_ = lean_ctor_get(v___y_91_, 0);
v_fileMap_166_ = lean_ctor_get(v___y_91_, 1);
v_suppressElabErrors_167_ = lean_ctor_get_uint8(v___y_91_, sizeof(void*)*10);
v___x_168_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_88_);
v___x_169_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg(v___x_168_, v___y_92_);
v_a_170_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_186_ == 0)
{
v___x_172_ = v___x_169_;
v_isShared_173_ = v_isSharedCheck_186_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_169_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_186_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
lean_inc_ref_n(v_fileMap_166_, 2);
v___x_174_ = l_Lean_FileMap_toPosition(v_fileMap_166_, v___y_161_);
lean_dec(v___y_161_);
v___x_175_ = l_Lean_FileMap_toPosition(v_fileMap_166_, v___y_164_);
lean_dec(v___y_164_);
v___x_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
v___x_177_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___closed__0));
if (v_suppressElabErrors_167_ == 0)
{
lean_del_object(v___x_172_);
v___y_95_ = v___x_176_;
v___y_96_ = v_a_170_;
v___y_97_ = v___x_177_;
v___y_98_ = v___x_174_;
v___y_99_ = v___y_162_;
v___y_100_ = v___y_163_;
v___y_101_ = v_fileName_165_;
v___y_102_ = v___y_92_;
goto v___jp_94_;
}
else
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___f_180_; uint8_t v___x_181_; 
v___x_178_ = lean_box(v_suppressElabErrors_167_);
v___x_179_ = lean_box(v___y_160_);
v___f_180_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_180_, 0, v___x_178_);
lean_closure_set(v___f_180_, 1, v___x_179_);
lean_inc(v_a_170_);
v___x_181_ = l_Lean_MessageData_hasTag(v___f_180_, v_a_170_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; lean_object* v___x_184_; 
lean_dec_ref_known(v___x_176_, 1);
lean_dec_ref(v___x_174_);
lean_dec(v_a_170_);
v___x_182_ = lean_box(0);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v___x_182_);
v___x_184_ = v___x_172_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_182_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
else
{
lean_del_object(v___x_172_);
v___y_95_ = v___x_176_;
v___y_96_ = v_a_170_;
v___y_97_ = v___x_177_;
v___y_98_ = v___x_174_;
v___y_99_ = v___y_162_;
v___y_100_ = v___y_163_;
v___y_101_ = v_fileName_165_;
v___y_102_ = v___y_92_;
goto v___jp_94_;
}
}
}
}
v___jp_187_:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_Syntax_getTailPos_x3f(v___y_189_, v___y_190_);
lean_dec(v___y_189_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_inc(v___y_192_);
v___y_160_ = v___y_188_;
v___y_161_ = v___y_192_;
v___y_162_ = v___y_190_;
v___y_163_ = v___y_191_;
v___y_164_ = v___y_192_;
goto v___jp_159_;
}
else
{
lean_object* v_val_194_; 
v_val_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc(v_val_194_);
lean_dec_ref_known(v___x_193_, 1);
v___y_160_ = v___y_188_;
v___y_161_ = v___y_192_;
v___y_162_ = v___y_190_;
v___y_163_ = v___y_191_;
v___y_164_ = v_val_194_;
goto v___jp_159_;
}
}
v___jp_195_:
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_Elab_Command_getRef___redArg(v___y_91_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v_a_200_; lean_object* v_ref_201_; lean_object* v___x_202_; 
v_a_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_a_200_);
lean_dec_ref_known(v___x_199_, 1);
v_ref_201_ = l_Lean_replaceRef(v_ref_87_, v_a_200_);
lean_dec(v_a_200_);
v___x_202_ = l_Lean_Syntax_getPos_x3f(v_ref_201_, v___y_197_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v___x_203_; 
v___x_203_ = lean_unsigned_to_nat(0u);
v___y_188_ = v___y_196_;
v___y_189_ = v_ref_201_;
v___y_190_ = v___y_197_;
v___y_191_ = v___y_198_;
v___y_192_ = v___x_203_;
goto v___jp_187_;
}
else
{
lean_object* v_val_204_; 
v_val_204_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_val_204_);
lean_dec_ref_known(v___x_202_, 1);
v___y_188_ = v___y_196_;
v___y_189_ = v_ref_201_;
v___y_190_ = v___y_197_;
v___y_191_ = v___y_198_;
v___y_192_ = v_val_204_;
goto v___jp_187_;
}
}
else
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
lean_dec_ref(v_msgData_88_);
v_a_205_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_212_ == 0)
{
v___x_207_ = v___x_199_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_199_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_a_205_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
v___jp_214_:
{
if (v___y_217_ == 0)
{
v___y_196_ = v___y_215_;
v___y_197_ = v___y_216_;
v___y_198_ = v_severity_89_;
goto v___jp_195_;
}
else
{
v___y_196_ = v___y_215_;
v___y_197_ = v___y_216_;
v___y_198_ = v___x_213_;
goto v___jp_195_;
}
}
v___jp_218_:
{
if (v___y_219_ == 0)
{
lean_object* v___x_220_; lean_object* v_scopes_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v_opts_224_; uint8_t v___x_225_; uint8_t v___x_226_; 
v___x_220_ = lean_st_ref_get(v___y_92_);
v_scopes_221_ = lean_ctor_get(v___x_220_, 2);
lean_inc(v_scopes_221_);
lean_dec(v___x_220_);
v___x_222_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_223_ = l_List_head_x21___redArg(v___x_222_, v_scopes_221_);
lean_dec(v_scopes_221_);
v_opts_224_ = lean_ctor_get(v___x_223_, 1);
lean_inc_ref(v_opts_224_);
lean_dec(v___x_223_);
v___x_225_ = 1;
v___x_226_ = l_Lean_instBEqMessageSeverity_beq(v_severity_89_, v___x_225_);
if (v___x_226_ == 0)
{
lean_dec_ref(v_opts_224_);
v___y_215_ = v___y_219_;
v___y_216_ = v___y_219_;
v___y_217_ = v___x_226_;
goto v___jp_214_;
}
else
{
lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_227_ = l_Lean_warningAsError;
v___x_228_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__3(v_opts_224_, v___x_227_);
lean_dec_ref(v_opts_224_);
v___y_215_ = v___y_219_;
v___y_216_ = v___y_219_;
v___y_217_ = v___x_228_;
goto v___jp_214_;
}
}
else
{
lean_object* v___x_229_; lean_object* v___x_230_; 
lean_dec_ref(v_msgData_88_);
v___x_229_ = lean_box(0);
v___x_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
return v___x_230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___boxed(lean_object* v_ref_233_, lean_object* v_msgData_234_, lean_object* v_severity_235_, lean_object* v_isSilent_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
uint8_t v_severity_boxed_240_; uint8_t v_isSilent_boxed_241_; lean_object* v_res_242_; 
v_severity_boxed_240_ = lean_unbox(v_severity_235_);
v_isSilent_boxed_241_ = lean_unbox(v_isSilent_236_);
v_res_242_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1(v_ref_233_, v_msgData_234_, v_severity_boxed_240_, v_isSilent_boxed_241_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v_ref_233_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1(lean_object* v_ref_243_, lean_object* v_msgData_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
uint8_t v___x_248_; uint8_t v___x_249_; lean_object* v___x_250_; 
v___x_248_ = 0;
v___x_249_ = 0;
v___x_250_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1(v_ref_243_, v_msgData_244_, v___x_248_, v___x_249_, v___y_245_, v___y_246_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1___boxed(lean_object* v_ref_251_, lean_object* v_msgData_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1(v_ref_251_, v_msgData_252_, v___y_253_, v___y_254_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec(v_ref_251_);
return v_res_256_;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___closed__5(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = ((lean_object*)(l_Lean_Elab_Time_elabTimeCmd___closed__4));
v___x_266_ = l_Lean_stringToMessageData(v___x_265_);
return v___x_266_;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___closed__7(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = ((lean_object*)(l_Lean_Elab_Time_elabTimeCmd___closed__6));
v___x_269_ = l_Lean_stringToMessageData(v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Time_elabTimeCmd(lean_object* v_x_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_274_ = ((lean_object*)(l_Lean_Elab_Time_elabTimeCmd___closed__3));
lean_inc(v_x_270_);
v___x_275_ = l_Lean_Syntax_isOfKind(v_x_270_, v___x_274_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; 
lean_dec(v_x_270_);
v___x_276_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg();
return v___x_276_;
}
else
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_277_ = lean_io_mono_ms_now();
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = l_Lean_Syntax_getArg(v_x_270_, v___x_278_);
v___x_280_ = l_Lean_Elab_Command_elabCommand(v___x_279_, v_a_271_, v_a_272_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_298_; 
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_298_ == 0)
{
lean_object* v_unused_299_; 
v_unused_299_ = lean_ctor_get(v___x_280_, 0);
lean_dec(v_unused_299_);
v___x_282_ = v___x_280_;
v_isShared_283_ = v_isSharedCheck_298_;
goto v_resetjp_281_;
}
else
{
lean_dec(v___x_280_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_298_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v_tk_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_284_ = lean_io_mono_ms_now();
v___x_285_ = lean_unsigned_to_nat(0u);
v_tk_286_ = l_Lean_Syntax_getArg(v_x_270_, v___x_285_);
lean_dec(v_x_270_);
v___x_287_ = lean_obj_once(&l_Lean_Elab_Time_elabTimeCmd___closed__5, &l_Lean_Elab_Time_elabTimeCmd___closed__5_once, _init_l_Lean_Elab_Time_elabTimeCmd___closed__5);
v___x_288_ = lean_nat_sub(v___x_284_, v___x_277_);
lean_dec(v___x_277_);
lean_dec(v___x_284_);
v___x_289_ = l_Nat_reprFast(v___x_288_);
if (v_isShared_283_ == 0)
{
lean_ctor_set_tag(v___x_282_, 3);
lean_ctor_set(v___x_282_, 0, v___x_289_);
v___x_291_ = v___x_282_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_289_);
v___x_291_ = v_reuseFailAlloc_297_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_292_ = l_Lean_MessageData_ofFormat(v___x_291_);
v___x_293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_287_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = lean_obj_once(&l_Lean_Elab_Time_elabTimeCmd___closed__7, &l_Lean_Elab_Time_elabTimeCmd___closed__7_once, _init_l_Lean_Elab_Time_elabTimeCmd___closed__7);
v___x_295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_293_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1(v_tk_286_, v___x_295_, v_a_271_, v_a_272_);
lean_dec(v_tk_286_);
return v___x_296_;
}
}
}
else
{
lean_dec(v___x_277_);
lean_dec(v_x_270_);
return v___x_280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Time_elabTimeCmd___boxed(lean_object* v_x_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Elab_Time_elabTimeCmd(v_x_300_, v_a_301_, v_a_302_);
lean_dec(v_a_302_);
lean_dec_ref(v_a_301_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2(lean_object* v_msgData_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg(v_msgData_305_, v___y_307_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2(v_msgData_310_, v___y_311_, v___y_312_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1(){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_324_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_325_ = ((lean_object*)(l_Lean_Elab_Time_elabTimeCmd___closed__3));
v___x_326_ = ((lean_object*)(l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3));
v___x_327_ = lean_alloc_closure((void*)(l_Lean_Elab_Time_elabTimeCmd___boxed), 4, 0);
v___x_328_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_324_, v___x_325_, v___x_326_, v___x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___boxed(lean_object* v_a_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1();
return v_res_330_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Time(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Time(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Time(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Time(builtin);
}
#ifdef __cplusplus
}
#endif

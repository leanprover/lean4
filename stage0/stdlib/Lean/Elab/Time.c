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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
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
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now();
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0(uint8_t v_suppressElabErrors_20_, lean_object* v_x_21_){
_start:
{
if (lean_obj_tag(v_x_21_) == 1)
{
lean_object* v_pre_22_; 
v_pre_22_ = lean_ctor_get(v_x_21_, 0);
if (lean_obj_tag(v_pre_22_) == 0)
{
lean_object* v_str_23_; lean_object* v___x_24_; uint8_t v___x_25_; 
v_str_23_ = lean_ctor_get(v_x_21_, 1);
v___x_24_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0___closed__0));
v___x_25_ = lean_string_dec_eq(v_str_23_, v___x_24_);
if (v___x_25_ == 0)
{
return v___x_25_;
}
else
{
return v_suppressElabErrors_20_;
}
}
else
{
uint8_t v___x_26_; 
v___x_26_ = 0;
return v___x_26_;
}
}
else
{
uint8_t v___x_27_; 
v___x_27_ = 0;
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_28_, lean_object* v_x_29_){
_start:
{
uint8_t v_suppressElabErrors_boxed_30_; uint8_t v_res_31_; lean_object* v_r_32_; 
v_suppressElabErrors_boxed_30_ = lean_unbox(v_suppressElabErrors_28_);
v_res_31_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0(v_suppressElabErrors_boxed_30_, v_x_29_);
lean_dec(v_x_29_);
v_r_32_ = lean_box(v_res_31_);
return v_r_32_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__3(lean_object* v_opts_33_, lean_object* v_opt_34_){
_start:
{
lean_object* v_name_35_; lean_object* v_defValue_36_; lean_object* v_map_37_; lean_object* v___x_38_; 
v_name_35_ = lean_ctor_get(v_opt_34_, 0);
v_defValue_36_ = lean_ctor_get(v_opt_34_, 1);
v_map_37_ = lean_ctor_get(v_opts_33_, 0);
v___x_38_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_37_, v_name_35_);
if (lean_obj_tag(v___x_38_) == 0)
{
uint8_t v___x_39_; 
v___x_39_ = lean_unbox(v_defValue_36_);
return v___x_39_;
}
else
{
lean_object* v_val_40_; 
v_val_40_ = lean_ctor_get(v___x_38_, 0);
lean_inc(v_val_40_);
lean_dec_ref_known(v___x_38_, 1);
if (lean_obj_tag(v_val_40_) == 1)
{
uint8_t v_v_41_; 
v_v_41_ = lean_ctor_get_uint8(v_val_40_, 0);
lean_dec_ref_known(v_val_40_, 0);
return v_v_41_;
}
else
{
uint8_t v___x_42_; 
lean_dec(v_val_40_);
v___x_42_ = lean_unbox(v_defValue_36_);
return v___x_42_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__3___boxed(lean_object* v_opts_43_, lean_object* v_opt_44_){
_start:
{
uint8_t v_res_45_; lean_object* v_r_46_; 
v_res_45_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__3(v_opts_43_, v_opt_44_);
lean_dec_ref(v_opt_44_);
lean_dec_ref(v_opts_43_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_47_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
return v___x_49_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_51_ = lean_unsigned_to_nat(0u);
v___x_52_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
lean_ctor_set(v___x_52_, 2, v___x_51_);
lean_ctor_set(v___x_52_, 3, v___x_51_);
lean_ctor_set(v___x_52_, 4, v___x_50_);
lean_ctor_set(v___x_52_, 5, v___x_50_);
lean_ctor_set(v___x_52_, 6, v___x_50_);
lean_ctor_set(v___x_52_, 7, v___x_50_);
lean_ctor_set(v___x_52_, 8, v___x_50_);
lean_ctor_set(v___x_52_, 9, v___x_50_);
lean_ctor_set(v___x_52_, 10, v___x_50_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_unsigned_to_nat(32u);
v___x_54_ = lean_mk_empty_array_with_capacity(v___x_53_);
v___x_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_56_ = ((size_t)5ULL);
v___x_57_ = lean_unsigned_to_nat(0u);
v___x_58_ = lean_unsigned_to_nat(32u);
v___x_59_ = lean_mk_empty_array_with_capacity(v___x_58_);
v___x_60_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3);
v___x_61_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set(v___x_61_, 1, v___x_59_);
lean_ctor_set(v___x_61_, 2, v___x_57_);
lean_ctor_set(v___x_61_, 3, v___x_57_);
lean_ctor_set_usize(v___x_61_, 4, v___x_56_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_62_ = lean_box(1);
v___x_63_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4);
v___x_64_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_65_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v___x_63_);
lean_ctor_set(v___x_65_, 2, v___x_62_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg(lean_object* v_msgData_66_, lean_object* v___y_67_){
_start:
{
lean_object* v___x_69_; lean_object* v_env_70_; uint8_t v___x_71_; lean_object* v_env_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v_scopes_75_; lean_object* v___x_76_; lean_object* v_opts_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_69_ = lean_st_ref_get(v___y_67_);
v_env_70_ = lean_ctor_get(v___x_69_, 0);
lean_inc_ref(v_env_70_);
lean_dec(v___x_69_);
v___x_71_ = 0;
v_env_72_ = l_Lean_Environment_setRecordingDeps(v_env_70_, v___x_71_);
v___x_73_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_74_ = lean_st_ref_get(v___y_67_);
v_scopes_75_ = lean_ctor_get(v___x_74_, 2);
lean_inc(v_scopes_75_);
lean_dec(v___x_74_);
v___x_76_ = l_List_head_x21___redArg(v___x_73_, v_scopes_75_);
lean_dec(v_scopes_75_);
v_opts_77_ = lean_ctor_get(v___x_76_, 1);
lean_inc_ref(v_opts_77_);
lean_dec(v___x_76_);
v___x_78_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_79_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5);
v___x_80_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_80_, 0, v_env_72_);
lean_ctor_set(v___x_80_, 1, v___x_78_);
lean_ctor_set(v___x_80_, 2, v___x_79_);
lean_ctor_set(v___x_80_, 3, v_opts_77_);
v___x_81_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v_msgData_66_);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg(v_msgData_83_, v___y_84_);
lean_dec(v___y_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1(lean_object* v_ref_88_, lean_object* v_msgData_89_, uint8_t v_severity_90_, uint8_t v_isSilent_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v___y_96_; uint8_t v___y_97_; lean_object* v___y_98_; lean_object* v___y_99_; lean_object* v___y_100_; uint8_t v___y_101_; lean_object* v___y_102_; lean_object* v___y_103_; lean_object* v___y_161_; uint8_t v___y_162_; uint8_t v___y_163_; lean_object* v___y_164_; uint8_t v___y_187_; lean_object* v___y_188_; uint8_t v___y_189_; lean_object* v___y_190_; uint8_t v___y_194_; uint8_t v___y_195_; uint8_t v___x_210_; uint8_t v___y_212_; uint8_t v___x_222_; 
v___x_210_ = 2;
v___x_222_ = l_Lean_instBEqMessageSeverity_beq(v_severity_90_, v___x_210_);
if (v___x_222_ == 0)
{
v___y_212_ = v___x_222_;
goto v___jp_211_;
}
else
{
uint8_t v___x_223_; 
lean_inc_ref(v_msgData_89_);
v___x_223_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_89_);
if (v___x_223_ == 0)
{
v___y_212_ = v___x_223_;
goto v___jp_211_;
}
else
{
lean_object* v___x_224_; lean_object* v___x_225_; 
lean_dec_ref(v_msgData_89_);
v___x_224_ = lean_box(0);
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
return v___x_225_;
}
}
v___jp_95_:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_Elab_Command_getScope___redArg(v___y_103_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v_currNamespace_106_; lean_object* v___x_107_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_a_105_);
lean_dec_ref_known(v___x_104_, 1);
v_currNamespace_106_ = lean_ctor_get(v_a_105_, 2);
lean_inc(v_currNamespace_106_);
lean_dec(v_a_105_);
v___x_107_ = l_Lean_Elab_Command_getScope___redArg(v___y_103_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_143_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_143_ == 0)
{
v___x_110_ = v___x_107_;
v_isShared_111_ = v_isSharedCheck_143_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_143_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v_openDecls_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v_env_117_; lean_object* v_messages_118_; lean_object* v_scopes_119_; lean_object* v_usedQuotCtxts_120_; lean_object* v_nextMacroScope_121_; lean_object* v_maxRecDepth_122_; lean_object* v_ngen_123_; lean_object* v_auxDeclNGen_124_; lean_object* v_infoState_125_; lean_object* v_traceState_126_; lean_object* v_snapshotTasks_127_; lean_object* v_prevLinterStates_128_; lean_object* v_codeQualityEntryTasks_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_142_; 
v_openDecls_112_ = lean_ctor_get(v_a_108_, 3);
lean_inc(v_openDecls_112_);
lean_dec(v_a_108_);
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v_currNamespace_106_);
lean_ctor_set(v___x_113_, 1, v_openDecls_112_);
v___x_114_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___y_100_);
lean_inc_ref(v___y_96_);
lean_inc_ref(v___y_99_);
v___x_115_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_115_, 0, v___y_99_);
lean_ctor_set(v___x_115_, 1, v___y_98_);
lean_ctor_set(v___x_115_, 2, v___y_102_);
lean_ctor_set(v___x_115_, 3, v___y_96_);
lean_ctor_set(v___x_115_, 4, v___x_114_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*5, v___y_101_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*5 + 1, v___y_97_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*5 + 2, v_isSilent_91_);
v___x_116_ = lean_st_ref_take(v___y_103_);
v_env_117_ = lean_ctor_get(v___x_116_, 0);
v_messages_118_ = lean_ctor_get(v___x_116_, 1);
v_scopes_119_ = lean_ctor_get(v___x_116_, 2);
v_usedQuotCtxts_120_ = lean_ctor_get(v___x_116_, 3);
v_nextMacroScope_121_ = lean_ctor_get(v___x_116_, 4);
v_maxRecDepth_122_ = lean_ctor_get(v___x_116_, 5);
v_ngen_123_ = lean_ctor_get(v___x_116_, 6);
v_auxDeclNGen_124_ = lean_ctor_get(v___x_116_, 7);
v_infoState_125_ = lean_ctor_get(v___x_116_, 8);
v_traceState_126_ = lean_ctor_get(v___x_116_, 9);
v_snapshotTasks_127_ = lean_ctor_get(v___x_116_, 10);
v_prevLinterStates_128_ = lean_ctor_get(v___x_116_, 11);
v_codeQualityEntryTasks_129_ = lean_ctor_get(v___x_116_, 12);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_142_ == 0)
{
v___x_131_ = v___x_116_;
v_isShared_132_ = v_isSharedCheck_142_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_codeQualityEntryTasks_129_);
lean_inc(v_prevLinterStates_128_);
lean_inc(v_snapshotTasks_127_);
lean_inc(v_traceState_126_);
lean_inc(v_infoState_125_);
lean_inc(v_auxDeclNGen_124_);
lean_inc(v_ngen_123_);
lean_inc(v_maxRecDepth_122_);
lean_inc(v_nextMacroScope_121_);
lean_inc(v_usedQuotCtxts_120_);
lean_inc(v_scopes_119_);
lean_inc(v_messages_118_);
lean_inc(v_env_117_);
lean_dec(v___x_116_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_142_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_133_ = lean_box(0);
v___x_134_ = l_Lean_MessageLog_add(v___x_115_, v_messages_118_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 1, v___x_134_);
v___x_136_ = v___x_131_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_env_117_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_141_, 2, v_scopes_119_);
lean_ctor_set(v_reuseFailAlloc_141_, 3, v_usedQuotCtxts_120_);
lean_ctor_set(v_reuseFailAlloc_141_, 4, v_nextMacroScope_121_);
lean_ctor_set(v_reuseFailAlloc_141_, 5, v_maxRecDepth_122_);
lean_ctor_set(v_reuseFailAlloc_141_, 6, v_ngen_123_);
lean_ctor_set(v_reuseFailAlloc_141_, 7, v_auxDeclNGen_124_);
lean_ctor_set(v_reuseFailAlloc_141_, 8, v_infoState_125_);
lean_ctor_set(v_reuseFailAlloc_141_, 9, v_traceState_126_);
lean_ctor_set(v_reuseFailAlloc_141_, 10, v_snapshotTasks_127_);
lean_ctor_set(v_reuseFailAlloc_141_, 11, v_prevLinterStates_128_);
lean_ctor_set(v_reuseFailAlloc_141_, 12, v_codeQualityEntryTasks_129_);
v___x_136_ = v_reuseFailAlloc_141_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_137_ = lean_st_ref_put(v___y_103_, v___x_136_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_133_);
v___x_139_ = v___x_110_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_133_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
}
else
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
lean_dec(v_currNamespace_106_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_100_);
lean_dec_ref(v___y_98_);
v_a_144_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v___x_107_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_107_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
else
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
lean_dec(v___y_102_);
lean_dec_ref(v___y_100_);
lean_dec_ref(v___y_98_);
v_a_152_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_159_ == 0)
{
v___x_154_ = v___x_104_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_104_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
v___jp_160_:
{
lean_object* v_fileName_165_; lean_object* v_fileMap_166_; uint8_t v_suppressElabErrors_167_; lean_object* v___x_168_; lean_object* v___f_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_185_; 
v_fileName_165_ = lean_ctor_get(v___y_92_, 0);
v_fileMap_166_ = lean_ctor_get(v___y_92_, 1);
v_suppressElabErrors_167_ = lean_ctor_get_uint8(v___y_92_, sizeof(void*)*10);
v___x_168_ = lean_box(v_suppressElabErrors_167_);
v___f_169_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_169_, 0, v___x_168_);
v___x_170_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_89_);
v___x_171_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg(v___x_170_, v___y_93_);
v_a_172_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_185_ == 0)
{
v___x_174_ = v___x_171_;
v_isShared_175_ = v_isSharedCheck_185_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_171_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_185_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
lean_inc_ref_n(v_fileMap_166_, 2);
v___x_176_ = l_Lean_FileMap_toPosition(v_fileMap_166_, v___y_161_);
lean_dec(v___y_161_);
v___x_177_ = l_Lean_FileMap_toPosition(v_fileMap_166_, v___y_164_);
lean_dec(v___y_164_);
v___x_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
v___x_179_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___closed__0));
if (v_suppressElabErrors_167_ == 0)
{
lean_del_object(v___x_174_);
lean_dec_ref(v___f_169_);
v___y_96_ = v___x_179_;
v___y_97_ = v___y_162_;
v___y_98_ = v___x_176_;
v___y_99_ = v_fileName_165_;
v___y_100_ = v_a_172_;
v___y_101_ = v___y_163_;
v___y_102_ = v___x_178_;
v___y_103_ = v___y_93_;
goto v___jp_95_;
}
else
{
uint8_t v___x_180_; 
lean_inc(v_a_172_);
v___x_180_ = l_Lean_MessageData_hasTag(v___f_169_, v_a_172_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_183_; 
lean_dec_ref_known(v___x_178_, 1);
lean_dec_ref(v___x_176_);
lean_dec(v_a_172_);
v___x_181_ = lean_box(0);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 0, v___x_181_);
v___x_183_ = v___x_174_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
else
{
lean_del_object(v___x_174_);
v___y_96_ = v___x_179_;
v___y_97_ = v___y_162_;
v___y_98_ = v___x_176_;
v___y_99_ = v_fileName_165_;
v___y_100_ = v_a_172_;
v___y_101_ = v___y_163_;
v___y_102_ = v___x_178_;
v___y_103_ = v___y_93_;
goto v___jp_95_;
}
}
}
}
v___jp_186_:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_Syntax_getTailPos_x3f(v___y_188_, v___y_189_);
lean_dec(v___y_188_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_inc(v___y_190_);
v___y_161_ = v___y_190_;
v___y_162_ = v___y_187_;
v___y_163_ = v___y_189_;
v___y_164_ = v___y_190_;
goto v___jp_160_;
}
else
{
lean_object* v_val_192_; 
v_val_192_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_val_192_);
lean_dec_ref_known(v___x_191_, 1);
v___y_161_ = v___y_190_;
v___y_162_ = v___y_187_;
v___y_163_ = v___y_189_;
v___y_164_ = v_val_192_;
goto v___jp_160_;
}
}
v___jp_193_:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_Elab_Command_getRef___redArg(v___y_92_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; lean_object* v_ref_198_; lean_object* v___x_199_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_a_197_);
lean_dec_ref_known(v___x_196_, 1);
v_ref_198_ = l_Lean_replaceRef(v_ref_88_, v_a_197_);
lean_dec(v_a_197_);
v___x_199_ = l_Lean_Syntax_getPos_x3f(v_ref_198_, v___y_194_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v___x_200_; 
v___x_200_ = lean_unsigned_to_nat(0u);
v___y_187_ = v___y_195_;
v___y_188_ = v_ref_198_;
v___y_189_ = v___y_194_;
v___y_190_ = v___x_200_;
goto v___jp_186_;
}
else
{
lean_object* v_val_201_; 
v_val_201_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_val_201_);
lean_dec_ref_known(v___x_199_, 1);
v___y_187_ = v___y_195_;
v___y_188_ = v_ref_198_;
v___y_189_ = v___y_194_;
v___y_190_ = v_val_201_;
goto v___jp_186_;
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec_ref(v_msgData_89_);
v_a_202_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_196_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_196_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
v___jp_211_:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v_scopes_215_; lean_object* v___x_216_; lean_object* v_opts_217_; uint8_t v___x_218_; uint8_t v___x_219_; 
v___x_213_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_214_ = lean_st_ref_get(v___y_93_);
v_scopes_215_ = lean_ctor_get(v___x_214_, 2);
lean_inc(v_scopes_215_);
lean_dec(v___x_214_);
v___x_216_ = l_List_head_x21___redArg(v___x_213_, v_scopes_215_);
lean_dec(v_scopes_215_);
v_opts_217_ = lean_ctor_get(v___x_216_, 1);
lean_inc_ref(v_opts_217_);
lean_dec(v___x_216_);
v___x_218_ = 1;
v___x_219_ = l_Lean_instBEqMessageSeverity_beq(v_severity_90_, v___x_218_);
if (v___x_219_ == 0)
{
lean_dec_ref(v_opts_217_);
v___y_194_ = v___y_212_;
v___y_195_ = v_severity_90_;
goto v___jp_193_;
}
else
{
lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_220_ = l_Lean_warningAsError;
v___x_221_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__3(v_opts_217_, v___x_220_);
lean_dec_ref(v_opts_217_);
if (v___x_221_ == 0)
{
v___y_194_ = v___y_212_;
v___y_195_ = v_severity_90_;
goto v___jp_193_;
}
else
{
v___y_194_ = v___y_212_;
v___y_195_ = v___x_210_;
goto v___jp_193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___boxed(lean_object* v_ref_226_, lean_object* v_msgData_227_, lean_object* v_severity_228_, lean_object* v_isSilent_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
uint8_t v_severity_boxed_233_; uint8_t v_isSilent_boxed_234_; lean_object* v_res_235_; 
v_severity_boxed_233_ = lean_unbox(v_severity_228_);
v_isSilent_boxed_234_ = lean_unbox(v_isSilent_229_);
v_res_235_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1(v_ref_226_, v_msgData_227_, v_severity_boxed_233_, v_isSilent_boxed_234_, v___y_230_, v___y_231_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v_ref_226_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1(lean_object* v_ref_236_, lean_object* v_msgData_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
uint8_t v___x_241_; uint8_t v___x_242_; lean_object* v___x_243_; 
v___x_241_ = 0;
v___x_242_ = 0;
v___x_243_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1(v_ref_236_, v_msgData_237_, v___x_241_, v___x_242_, v___y_238_, v___y_239_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1___boxed(lean_object* v_ref_244_, lean_object* v_msgData_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1(v_ref_244_, v_msgData_245_, v___y_246_, v___y_247_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v_ref_244_);
return v_res_249_;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___closed__5(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = ((lean_object*)(l_Lean_Elab_Time_elabTimeCmd___closed__4));
v___x_259_ = l_Lean_stringToMessageData(v___x_258_);
return v___x_259_;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___closed__7(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = ((lean_object*)(l_Lean_Elab_Time_elabTimeCmd___closed__6));
v___x_262_ = l_Lean_stringToMessageData(v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Time_elabTimeCmd(lean_object* v_x_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_267_ = ((lean_object*)(l_Lean_Elab_Time_elabTimeCmd___closed__3));
lean_inc(v_x_263_);
v___x_268_ = l_Lean_Syntax_isOfKind(v_x_263_, v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
lean_dec(v_x_263_);
v___x_269_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg();
return v___x_269_;
}
else
{
lean_object* v___x_270_; lean_object* v_tk_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_270_ = lean_unsigned_to_nat(0u);
v_tk_271_ = l_Lean_Syntax_getArg(v_x_263_, v___x_270_);
v___x_272_ = lean_unsigned_to_nat(1u);
v___x_273_ = l_Lean_Syntax_getArg(v_x_263_, v___x_272_);
lean_dec(v_x_263_);
v___x_274_ = lean_io_mono_ms_now();
v___x_275_ = l_Lean_Elab_Command_elabCommand(v___x_273_, v_a_264_, v_a_265_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_291_; 
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_291_ == 0)
{
lean_object* v_unused_292_; 
v_unused_292_ = lean_ctor_get(v___x_275_, 0);
lean_dec(v_unused_292_);
v___x_277_ = v___x_275_;
v_isShared_278_ = v_isSharedCheck_291_;
goto v_resetjp_276_;
}
else
{
lean_dec(v___x_275_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_291_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_279_ = lean_io_mono_ms_now();
v___x_280_ = lean_obj_once(&l_Lean_Elab_Time_elabTimeCmd___closed__5, &l_Lean_Elab_Time_elabTimeCmd___closed__5_once, _init_l_Lean_Elab_Time_elabTimeCmd___closed__5);
v___x_281_ = lean_nat_sub(v___x_279_, v___x_274_);
lean_dec(v___x_274_);
lean_dec(v___x_279_);
v___x_282_ = l_Nat_reprFast(v___x_281_);
if (v_isShared_278_ == 0)
{
lean_ctor_set_tag(v___x_277_, 3);
lean_ctor_set(v___x_277_, 0, v___x_282_);
v___x_284_ = v___x_277_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_282_);
v___x_284_ = v_reuseFailAlloc_290_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_285_ = l_Lean_MessageData_ofFormat(v___x_284_);
v___x_286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_280_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = lean_obj_once(&l_Lean_Elab_Time_elabTimeCmd___closed__7, &l_Lean_Elab_Time_elabTimeCmd___closed__7_once, _init_l_Lean_Elab_Time_elabTimeCmd___closed__7);
v___x_288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1(v_tk_271_, v___x_288_, v_a_264_, v_a_265_);
lean_dec(v_tk_271_);
return v___x_289_;
}
}
}
else
{
lean_dec(v___x_274_);
lean_dec(v_tk_271_);
return v___x_275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Time_elabTimeCmd___boxed(lean_object* v_x_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Elab_Time_elabTimeCmd(v_x_293_, v_a_294_, v_a_295_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2(lean_object* v_msgData_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg(v_msgData_298_, v___y_300_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2(v_msgData_303_, v___y_304_, v___y_305_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1(){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_317_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_318_ = ((lean_object*)(l_Lean_Elab_Time_elabTimeCmd___closed__3));
v___x_319_ = ((lean_object*)(l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3));
v___x_320_ = lean_alloc_closure((void*)(l_Lean_Elab_Time_elabTimeCmd___boxed), 4, 0);
v___x_321_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_317_, v___x_318_, v___x_319_, v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___boxed(lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1();
return v_res_323_;
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

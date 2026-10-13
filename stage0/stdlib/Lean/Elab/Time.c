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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
uint8_t v_suppressElabErrors_boxed_30_; uint8_t v___y_2732__boxed_31_; uint8_t v_res_32_; lean_object* v_r_33_; 
v_suppressElabErrors_boxed_30_ = lean_unbox(v_suppressElabErrors_27_);
v___y_2732__boxed_31_ = lean_unbox(v___y_28_);
v_res_32_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0(v_suppressElabErrors_boxed_30_, v___y_2732__boxed_31_, v_x_29_);
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
v___x_48_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_51_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_52_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_53_ = lean_unsigned_to_nat(0u);
v___x_54_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
lean_ctor_set(v___x_54_, 1, v___x_53_);
lean_ctor_set(v___x_54_, 2, v___x_53_);
lean_ctor_set(v___x_54_, 3, v___x_53_);
lean_ctor_set(v___x_54_, 4, v___x_52_);
lean_ctor_set(v___x_54_, 5, v___x_52_);
lean_ctor_set(v___x_54_, 6, v___x_52_);
lean_ctor_set(v___x_54_, 7, v___x_52_);
lean_ctor_set(v___x_54_, 8, v___x_52_);
lean_ctor_set(v___x_54_, 9, v___x_52_);
lean_ctor_set(v___x_54_, 10, v___x_52_);
lean_ctor_set(v___x_54_, 11, v___x_51_);
return v___x_54_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = lean_unsigned_to_nat(32u);
v___x_56_ = lean_mk_empty_array_with_capacity(v___x_55_);
v___x_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
return v___x_57_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_58_ = ((size_t)5ULL);
v___x_59_ = lean_unsigned_to_nat(0u);
v___x_60_ = lean_unsigned_to_nat(32u);
v___x_61_ = lean_mk_empty_array_with_capacity(v___x_60_);
v___x_62_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3);
v___x_63_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_63_, 0, v___x_62_);
lean_ctor_set(v___x_63_, 1, v___x_61_);
lean_ctor_set(v___x_63_, 2, v___x_59_);
lean_ctor_set(v___x_63_, 3, v___x_59_);
lean_ctor_set_usize(v___x_63_, 4, v___x_58_);
return v___x_63_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_64_ = lean_box(1);
v___x_65_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4);
v___x_66_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_67_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v___x_65_);
lean_ctor_set(v___x_67_, 2, v___x_64_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg(lean_object* v_msgData_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; lean_object* v_env_72_; uint8_t v___x_73_; lean_object* v_env_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v_scopes_77_; lean_object* v___x_78_; lean_object* v_opts_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_71_ = lean_st_ref_get(v___y_69_);
v_env_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc_ref(v_env_72_);
lean_dec(v___x_71_);
v___x_73_ = 0;
v_env_74_ = l_Lean_Environment_setRecordingDeps(v_env_72_, v___x_73_);
v___x_75_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_76_ = lean_st_ref_get(v___y_69_);
v_scopes_77_ = lean_ctor_get(v___x_76_, 2);
lean_inc(v_scopes_77_);
lean_dec(v___x_76_);
v___x_78_ = l_List_head_x21___redArg(v___x_75_, v_scopes_77_);
lean_dec(v_scopes_77_);
v_opts_79_ = lean_ctor_get(v___x_78_, 1);
lean_inc_ref(v_opts_79_);
lean_dec(v___x_78_);
v___x_80_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_81_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5);
v___x_82_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_82_, 0, v_env_74_);
lean_ctor_set(v___x_82_, 1, v___x_80_);
lean_ctor_set(v___x_82_, 2, v___x_81_);
lean_ctor_set(v___x_82_, 3, v_opts_79_);
v___x_83_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v_msgData_68_);
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg(v_msgData_85_, v___y_86_);
lean_dec(v___y_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1(lean_object* v_ref_90_, lean_object* v_msgData_91_, uint8_t v_severity_92_, uint8_t v_isSilent_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v___y_98_; lean_object* v___y_99_; lean_object* v___y_100_; uint8_t v___y_101_; uint8_t v___y_102_; lean_object* v___y_103_; lean_object* v___y_104_; lean_object* v___y_105_; uint8_t v___y_163_; lean_object* v___y_164_; uint8_t v___y_165_; uint8_t v___y_166_; lean_object* v___y_167_; uint8_t v___y_191_; lean_object* v___y_192_; uint8_t v___y_193_; uint8_t v___y_194_; lean_object* v___y_195_; uint8_t v___y_199_; uint8_t v___y_200_; uint8_t v___y_201_; uint8_t v___x_216_; uint8_t v___y_218_; uint8_t v___y_219_; uint8_t v___y_220_; uint8_t v___y_222_; uint8_t v___x_234_; 
v___x_216_ = 2;
v___x_234_ = l_Lean_instBEqMessageSeverity_beq(v_severity_92_, v___x_216_);
if (v___x_234_ == 0)
{
v___y_222_ = v___x_234_;
goto v___jp_221_;
}
else
{
uint8_t v___x_235_; 
lean_inc_ref(v_msgData_91_);
v___x_235_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_91_);
v___y_222_ = v___x_235_;
goto v___jp_221_;
}
v___jp_97_:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Elab_Command_getScope___redArg(v___y_105_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; lean_object* v_currNamespace_108_; lean_object* v___x_109_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc(v_a_107_);
lean_dec_ref_known(v___x_106_, 1);
v_currNamespace_108_ = lean_ctor_get(v_a_107_, 2);
lean_inc(v_currNamespace_108_);
lean_dec(v_a_107_);
v___x_109_ = l_Lean_Elab_Command_getScope___redArg(v___y_105_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_145_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_145_ == 0)
{
v___x_112_ = v___x_109_;
v_isShared_113_ = v_isSharedCheck_145_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_109_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_145_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v_openDecls_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v_env_119_; lean_object* v_messages_120_; lean_object* v_scopes_121_; lean_object* v_usedQuotCtxts_122_; lean_object* v_nextMacroScope_123_; lean_object* v_maxRecDepth_124_; lean_object* v_ngen_125_; lean_object* v_auxDeclNGen_126_; lean_object* v_infoState_127_; lean_object* v_traceState_128_; lean_object* v_snapshotTasks_129_; lean_object* v_prevLinterStates_130_; lean_object* v_codeQualityEntryTasks_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_144_; 
v_openDecls_114_ = lean_ctor_get(v_a_110_, 3);
lean_inc(v_openDecls_114_);
lean_dec(v_a_110_);
v___x_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_115_, 0, v_currNamespace_108_);
lean_ctor_set(v___x_115_, 1, v_openDecls_114_);
v___x_116_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v___y_104_);
lean_inc_ref(v___y_99_);
lean_inc_ref(v___y_103_);
v___x_117_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_117_, 0, v___y_103_);
lean_ctor_set(v___x_117_, 1, v___y_98_);
lean_ctor_set(v___x_117_, 2, v___y_100_);
lean_ctor_set(v___x_117_, 3, v___y_99_);
lean_ctor_set(v___x_117_, 4, v___x_116_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*5, v___y_102_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*5 + 1, v___y_101_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*5 + 2, v_isSilent_93_);
v___x_118_ = lean_st_ref_take(v___y_105_);
v_env_119_ = lean_ctor_get(v___x_118_, 0);
v_messages_120_ = lean_ctor_get(v___x_118_, 1);
v_scopes_121_ = lean_ctor_get(v___x_118_, 2);
v_usedQuotCtxts_122_ = lean_ctor_get(v___x_118_, 3);
v_nextMacroScope_123_ = lean_ctor_get(v___x_118_, 4);
v_maxRecDepth_124_ = lean_ctor_get(v___x_118_, 5);
v_ngen_125_ = lean_ctor_get(v___x_118_, 6);
v_auxDeclNGen_126_ = lean_ctor_get(v___x_118_, 7);
v_infoState_127_ = lean_ctor_get(v___x_118_, 8);
v_traceState_128_ = lean_ctor_get(v___x_118_, 9);
v_snapshotTasks_129_ = lean_ctor_get(v___x_118_, 10);
v_prevLinterStates_130_ = lean_ctor_get(v___x_118_, 11);
v_codeQualityEntryTasks_131_ = lean_ctor_get(v___x_118_, 12);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_144_ == 0)
{
v___x_133_ = v___x_118_;
v_isShared_134_ = v_isSharedCheck_144_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_codeQualityEntryTasks_131_);
lean_inc(v_prevLinterStates_130_);
lean_inc(v_snapshotTasks_129_);
lean_inc(v_traceState_128_);
lean_inc(v_infoState_127_);
lean_inc(v_auxDeclNGen_126_);
lean_inc(v_ngen_125_);
lean_inc(v_maxRecDepth_124_);
lean_inc(v_nextMacroScope_123_);
lean_inc(v_usedQuotCtxts_122_);
lean_inc(v_scopes_121_);
lean_inc(v_messages_120_);
lean_inc(v_env_119_);
lean_dec(v___x_118_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_144_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_135_ = lean_box(0);
v___x_136_ = l_Lean_MessageLog_add(v___x_117_, v_messages_120_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v___x_136_);
v___x_138_ = v___x_133_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_env_119_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v___x_136_);
lean_ctor_set(v_reuseFailAlloc_143_, 2, v_scopes_121_);
lean_ctor_set(v_reuseFailAlloc_143_, 3, v_usedQuotCtxts_122_);
lean_ctor_set(v_reuseFailAlloc_143_, 4, v_nextMacroScope_123_);
lean_ctor_set(v_reuseFailAlloc_143_, 5, v_maxRecDepth_124_);
lean_ctor_set(v_reuseFailAlloc_143_, 6, v_ngen_125_);
lean_ctor_set(v_reuseFailAlloc_143_, 7, v_auxDeclNGen_126_);
lean_ctor_set(v_reuseFailAlloc_143_, 8, v_infoState_127_);
lean_ctor_set(v_reuseFailAlloc_143_, 9, v_traceState_128_);
lean_ctor_set(v_reuseFailAlloc_143_, 10, v_snapshotTasks_129_);
lean_ctor_set(v_reuseFailAlloc_143_, 11, v_prevLinterStates_130_);
lean_ctor_set(v_reuseFailAlloc_143_, 12, v_codeQualityEntryTasks_131_);
v___x_138_ = v_reuseFailAlloc_143_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_139_; lean_object* v___x_141_; 
v___x_139_ = lean_st_ref_put(v___y_105_, v___x_138_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 0, v___x_135_);
v___x_141_ = v___x_112_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_135_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
else
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
lean_dec(v_currNamespace_108_);
lean_dec_ref(v___y_104_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_98_);
v_a_146_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_109_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_109_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
lean_dec_ref(v___y_104_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_98_);
v_a_154_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_106_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_106_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
v___jp_162_:
{
lean_object* v_fileName_168_; lean_object* v_fileMap_169_; uint8_t v_suppressElabErrors_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___f_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_189_; 
v_fileName_168_ = lean_ctor_get(v___y_94_, 0);
v_fileMap_169_ = lean_ctor_get(v___y_94_, 1);
v_suppressElabErrors_170_ = lean_ctor_get_uint8(v___y_94_, sizeof(void*)*10);
v___x_171_ = lean_box(v_suppressElabErrors_170_);
v___x_172_ = lean_box(v___y_163_);
v___f_173_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_173_, 0, v___x_171_);
lean_closure_set(v___f_173_, 1, v___x_172_);
v___x_174_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_91_);
v___x_175_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg(v___x_174_, v___y_95_);
v_a_176_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_189_ == 0)
{
v___x_178_ = v___x_175_;
v_isShared_179_ = v_isSharedCheck_189_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_175_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_189_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
lean_inc_ref_n(v_fileMap_169_, 2);
v___x_180_ = l_Lean_FileMap_toPosition(v_fileMap_169_, v___y_164_);
lean_dec(v___y_164_);
v___x_181_ = l_Lean_FileMap_toPosition(v_fileMap_169_, v___y_167_);
lean_dec(v___y_167_);
v___x_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
v___x_183_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___closed__0));
if (v_suppressElabErrors_170_ == 0)
{
lean_del_object(v___x_178_);
lean_dec_ref(v___f_173_);
v___y_98_ = v___x_180_;
v___y_99_ = v___x_183_;
v___y_100_ = v___x_182_;
v___y_101_ = v___y_165_;
v___y_102_ = v___y_166_;
v___y_103_ = v_fileName_168_;
v___y_104_ = v_a_176_;
v___y_105_ = v___y_95_;
goto v___jp_97_;
}
else
{
uint8_t v___x_184_; 
lean_inc(v_a_176_);
v___x_184_ = l_Lean_MessageData_hasTag(v___f_173_, v_a_176_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; lean_object* v___x_187_; 
lean_dec_ref_known(v___x_182_, 1);
lean_dec_ref(v___x_180_);
lean_dec(v_a_176_);
v___x_185_ = lean_box(0);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_185_);
v___x_187_ = v___x_178_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_185_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
else
{
lean_del_object(v___x_178_);
v___y_98_ = v___x_180_;
v___y_99_ = v___x_183_;
v___y_100_ = v___x_182_;
v___y_101_ = v___y_165_;
v___y_102_ = v___y_166_;
v___y_103_ = v_fileName_168_;
v___y_104_ = v_a_176_;
v___y_105_ = v___y_95_;
goto v___jp_97_;
}
}
}
}
v___jp_190_:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_Syntax_getTailPos_x3f(v___y_192_, v___y_194_);
lean_dec(v___y_192_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_inc(v___y_195_);
v___y_163_ = v___y_191_;
v___y_164_ = v___y_195_;
v___y_165_ = v___y_193_;
v___y_166_ = v___y_194_;
v___y_167_ = v___y_195_;
goto v___jp_162_;
}
else
{
lean_object* v_val_197_; 
v_val_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_val_197_);
lean_dec_ref_known(v___x_196_, 1);
v___y_163_ = v___y_191_;
v___y_164_ = v___y_195_;
v___y_165_ = v___y_193_;
v___y_166_ = v___y_194_;
v___y_167_ = v_val_197_;
goto v___jp_162_;
}
}
v___jp_198_:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_Elab_Command_getRef___redArg(v___y_94_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; lean_object* v_ref_204_; lean_object* v___x_205_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_a_203_);
lean_dec_ref_known(v___x_202_, 1);
v_ref_204_ = l_Lean_replaceRef(v_ref_90_, v_a_203_);
lean_dec(v_a_203_);
v___x_205_ = l_Lean_Syntax_getPos_x3f(v_ref_204_, v___y_200_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v___x_206_; 
v___x_206_ = lean_unsigned_to_nat(0u);
v___y_191_ = v___y_199_;
v___y_192_ = v_ref_204_;
v___y_193_ = v___y_201_;
v___y_194_ = v___y_200_;
v___y_195_ = v___x_206_;
goto v___jp_190_;
}
else
{
lean_object* v_val_207_; 
v_val_207_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_val_207_);
lean_dec_ref_known(v___x_205_, 1);
v___y_191_ = v___y_199_;
v___y_192_ = v_ref_204_;
v___y_193_ = v___y_201_;
v___y_194_ = v___y_200_;
v___y_195_ = v_val_207_;
goto v___jp_190_;
}
}
else
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
lean_dec_ref(v_msgData_91_);
v_a_208_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_215_ == 0)
{
v___x_210_ = v___x_202_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_202_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_208_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
v___jp_217_:
{
if (v___y_220_ == 0)
{
v___y_199_ = v___y_218_;
v___y_200_ = v___y_219_;
v___y_201_ = v_severity_92_;
goto v___jp_198_;
}
else
{
v___y_199_ = v___y_218_;
v___y_200_ = v___y_219_;
v___y_201_ = v___x_216_;
goto v___jp_198_;
}
}
v___jp_221_:
{
if (v___y_222_ == 0)
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v_scopes_225_; lean_object* v___x_226_; lean_object* v_opts_227_; uint8_t v___x_228_; uint8_t v___x_229_; 
v___x_223_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_224_ = lean_st_ref_get(v___y_95_);
v_scopes_225_ = lean_ctor_get(v___x_224_, 2);
lean_inc(v_scopes_225_);
lean_dec(v___x_224_);
v___x_226_ = l_List_head_x21___redArg(v___x_223_, v_scopes_225_);
lean_dec(v_scopes_225_);
v_opts_227_ = lean_ctor_get(v___x_226_, 1);
lean_inc_ref(v_opts_227_);
lean_dec(v___x_226_);
v___x_228_ = 1;
v___x_229_ = l_Lean_instBEqMessageSeverity_beq(v_severity_92_, v___x_228_);
if (v___x_229_ == 0)
{
lean_dec_ref(v_opts_227_);
v___y_218_ = v___y_222_;
v___y_219_ = v___y_222_;
v___y_220_ = v___x_229_;
goto v___jp_217_;
}
else
{
lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_230_ = l_Lean_warningAsError;
v___x_231_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__3(v_opts_227_, v___x_230_);
lean_dec_ref(v_opts_227_);
v___y_218_ = v___y_222_;
v___y_219_ = v___y_222_;
v___y_220_ = v___x_231_;
goto v___jp_217_;
}
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec_ref(v_msgData_91_);
v___x_232_ = lean_box(0);
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
return v___x_233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___boxed(lean_object* v_ref_236_, lean_object* v_msgData_237_, lean_object* v_severity_238_, lean_object* v_isSilent_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
uint8_t v_severity_boxed_243_; uint8_t v_isSilent_boxed_244_; lean_object* v_res_245_; 
v_severity_boxed_243_ = lean_unbox(v_severity_238_);
v_isSilent_boxed_244_ = lean_unbox(v_isSilent_239_);
v_res_245_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1(v_ref_236_, v_msgData_237_, v_severity_boxed_243_, v_isSilent_boxed_244_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v_ref_236_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1(lean_object* v_ref_246_, lean_object* v_msgData_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
uint8_t v___x_251_; uint8_t v___x_252_; lean_object* v___x_253_; 
v___x_251_ = 0;
v___x_252_ = 0;
v___x_253_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1(v_ref_246_, v_msgData_247_, v___x_251_, v___x_252_, v___y_248_, v___y_249_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1___boxed(lean_object* v_ref_254_, lean_object* v_msgData_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1(v_ref_254_, v_msgData_255_, v___y_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v_ref_254_);
return v_res_259_;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___closed__5(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = ((lean_object*)(l_Lean_Elab_Time_elabTimeCmd___closed__4));
v___x_269_ = l_Lean_stringToMessageData(v___x_268_);
return v___x_269_;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___closed__7(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = ((lean_object*)(l_Lean_Elab_Time_elabTimeCmd___closed__6));
v___x_272_ = l_Lean_stringToMessageData(v___x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Time_elabTimeCmd(lean_object* v_x_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = ((lean_object*)(l_Lean_Elab_Time_elabTimeCmd___closed__3));
lean_inc(v_x_273_);
v___x_278_ = l_Lean_Syntax_isOfKind(v_x_273_, v___x_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; 
lean_dec(v_x_273_);
v___x_279_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg();
return v___x_279_;
}
else
{
lean_object* v___x_280_; lean_object* v_tk_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_280_ = lean_unsigned_to_nat(0u);
v_tk_281_ = l_Lean_Syntax_getArg(v_x_273_, v___x_280_);
v___x_282_ = lean_unsigned_to_nat(1u);
v___x_283_ = l_Lean_Syntax_getArg(v_x_273_, v___x_282_);
lean_dec(v_x_273_);
v___x_284_ = lean_io_mono_ms_now();
v___x_285_ = l_Lean_Elab_Command_elabCommand(v___x_283_, v_a_274_, v_a_275_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_301_; 
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; 
v_unused_302_ = lean_ctor_get(v___x_285_, 0);
lean_dec(v_unused_302_);
v___x_287_ = v___x_285_;
v_isShared_288_ = v_isSharedCheck_301_;
goto v_resetjp_286_;
}
else
{
lean_dec(v___x_285_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_301_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_289_ = lean_io_mono_ms_now();
v___x_290_ = lean_obj_once(&l_Lean_Elab_Time_elabTimeCmd___closed__5, &l_Lean_Elab_Time_elabTimeCmd___closed__5_once, _init_l_Lean_Elab_Time_elabTimeCmd___closed__5);
v___x_291_ = lean_nat_sub(v___x_289_, v___x_284_);
lean_dec(v___x_284_);
lean_dec(v___x_289_);
v___x_292_ = l_Nat_reprFast(v___x_291_);
if (v_isShared_288_ == 0)
{
lean_ctor_set_tag(v___x_287_, 3);
lean_ctor_set(v___x_287_, 0, v___x_292_);
v___x_294_ = v___x_287_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_300_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_295_ = l_Lean_MessageData_ofFormat(v___x_294_);
v___x_296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_290_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = lean_obj_once(&l_Lean_Elab_Time_elabTimeCmd___closed__7, &l_Lean_Elab_Time_elabTimeCmd___closed__7_once, _init_l_Lean_Elab_Time_elabTimeCmd___closed__7);
v___x_298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1(v_tk_281_, v___x_298_, v_a_274_, v_a_275_);
lean_dec(v_tk_281_);
return v___x_299_;
}
}
}
else
{
lean_dec(v___x_284_);
lean_dec(v_tk_281_);
return v___x_285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Time_elabTimeCmd___boxed(lean_object* v_x_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_Elab_Time_elabTimeCmd(v_x_303_, v_a_304_, v_a_305_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2(lean_object* v_msgData_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg(v_msgData_308_, v___y_310_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2(v_msgData_313_, v___y_314_, v___y_315_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1(){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_327_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_328_ = ((lean_object*)(l_Lean_Elab_Time_elabTimeCmd___closed__3));
v___x_329_ = ((lean_object*)(l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3));
v___x_330_ = lean_alloc_closure((void*)(l_Lean_Elab_Time_elabTimeCmd___boxed), 4, 0);
v___x_331_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_327_, v___x_328_, v___x_329_, v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___boxed(lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1();
return v_res_333_;
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

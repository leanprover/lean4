// Lean compiler output
// Module: Lake.Load.Package
// Imports: public import Lake.Load.Config public import Lake.Config.Package import Lake.Util.IO import Lake.Load.Lean import Lake.Load.Toml
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
static const lean_string_object l_Lake_configFileExists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lake_configFileExists___closed__0 = (const lean_object*)&l_Lake_configFileExists___closed__0_value;
static const lean_string_object l_Lake_configFileExists___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "toml"};
static const lean_object* l_Lake_configFileExists___closed__1 = (const lean_object*)&l_Lake_configFileExists___closed__1_value;
lean_object* l_System_FilePath_extension(lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
LEAN_EXPORT uint8_t l_Lake_configFileExists(lean_object*);
LEAN_EXPORT lean_object* l_Lake_configFileExists___boxed(lean_object*, lean_object*);
lean_object* l_Lake_resolvePath(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_realConfigFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_realConfigFile___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__1(lean_object*);
static const lean_string_object l_Lake_loadPackageCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = ": configuration has unsupported file extension: "};
static const lean_object* l_Lake_loadPackageCore___closed__0 = (const lean_object*)&l_Lake_loadPackageCore___closed__0_value;
static const lean_closure_object l_Lake_loadPackageCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_loadPackageCore___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_loadPackageCore___closed__1 = (const lean_object*)&l_Lake_loadPackageCore___closed__1_value;
static const lean_closure_object l_Lake_loadPackageCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_loadPackageCore___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_loadPackageCore___closed__2 = (const lean_object*)&l_Lake_loadPackageCore___closed__2_value;
static const lean_string_object l_Lake_loadPackageCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = ": configuration file not found: "};
static const lean_object* l_Lake_loadPackageCore___closed__3 = (const lean_object*)&l_Lake_loadPackageCore___closed__3_value;
static const lean_string_object l_Lake_loadPackageCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lake_loadPackageCore___closed__4 = (const lean_object*)&l_Lake_loadPackageCore___closed__4_value;
static const lean_string_object l_Lake_loadPackageCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " and "};
static const lean_object* l_Lake_loadPackageCore___closed__5 = (const lean_object*)&l_Lake_loadPackageCore___closed__5_value;
static const lean_string_object l_Lake_loadPackageCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = " are both present; using "};
static const lean_object* l_Lake_loadPackageCore___closed__6 = (const lean_object*)&l_Lake_loadPackageCore___closed__6_value;
static const lean_string_object l_Lake_loadPackageCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = ": no configuration file with a supported extension:\n"};
static const lean_object* l_Lake_loadPackageCore___closed__7 = (const lean_object*)&l_Lake_loadPackageCore___closed__7_value;
static const lean_string_object l_Lake_loadPackageCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lake_loadPackageCore___closed__8 = (const lean_object*)&l_Lake_loadPackageCore___closed__8_value;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_loadTomlConfig(lean_object*, lean_object*);
lean_object* l_Lake_loadLeanConfig(lean_object*, lean_object*);
lean_object* l_Prod_map___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackageCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_loadPackage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "[root]"};
static const lean_object* l_Lake_loadPackage___closed__0 = (const lean_object*)&l_Lake_loadPackage___closed__0_value;
extern lean_object* l_Lean_searchPathRef;
lean_object* l_Lake_Env_leanSearchPath(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackage___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_configFileExists(lean_object* x_1) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_1);
x_3 = l_System_FilePath_extension(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = ((lean_object*)(l_Lake_configFileExists___closed__0));
lean_inc_ref(x_1);
x_5 = l_System_FilePath_addExtension(x_1, x_4);
x_6 = l_System_FilePath_pathExists(x_5);
lean_dec_ref(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = ((lean_object*)(l_Lake_configFileExists___closed__1));
x_8 = l_System_FilePath_addExtension(x_1, x_7);
x_9 = l_System_FilePath_pathExists(x_8);
lean_dec_ref(x_8);
return x_9;
}
else
{
lean_dec_ref(x_1);
return x_6;
}
}
else
{
uint8_t x_10; 
lean_dec_ref(x_3);
x_10 = l_System_FilePath_pathExists(x_1);
lean_dec_ref(x_1);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_configFileExists___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_configFileExists(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_realConfigFile(lean_object* x_1) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_1);
x_3 = l_System_FilePath_extension(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = ((lean_object*)(l_Lake_configFileExists___closed__0));
lean_inc_ref(x_1);
x_5 = l_System_FilePath_addExtension(x_1, x_4);
x_6 = l_Lake_resolvePath(x_5);
x_7 = lean_string_utf8_byte_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_dec_ref(x_1);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_6);
x_10 = ((lean_object*)(l_Lake_configFileExists___closed__1));
x_11 = l_System_FilePath_addExtension(x_1, x_10);
x_12 = l_Lake_resolvePath(x_11);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec_ref(x_3);
x_13 = l_Lake_resolvePath(x_1);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lake_realConfigFile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_realConfigFile(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_loadPackageCore___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_192; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_ctor_get(x_2, 4);
x_10 = lean_ctor_get(x_2, 5);
x_11 = lean_ctor_get(x_2, 6);
x_12 = lean_ctor_get(x_2, 7);
x_13 = lean_ctor_get(x_2, 8);
x_14 = lean_ctor_get(x_2, 9);
x_15 = lean_ctor_get(x_2, 10);
x_16 = lean_ctor_get(x_2, 11);
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*14);
x_18 = lean_ctor_get_uint8(x_2, sizeof(void*)*14 + 1);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*14 + 2);
x_20 = lean_ctor_get(x_2, 12);
x_21 = lean_ctor_get(x_2, 13);
x_192 = !lean_is_exclusive(x_2);
if (x_192 == 0)
{
x_22 = x_2;
x_23 = x_192;
goto block_191;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_22 = lean_box(0);
x_23 = x_192;
goto block_191;
}
block_191:
{
lean_object* x_24; 
lean_inc_ref(x_12);
x_24 = l_System_FilePath_extension(x_12);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
lean_inc_ref(x_13);
x_26 = l_Lake_resolvePath(x_13);
x_27 = lean_string_utf8_byte_size(x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_eq(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec_ref(x_13);
lean_inc_ref(x_26);
if (x_23 == 0)
{
lean_ctor_set(x_22, 8, x_26);
x_30 = x_22;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 14, 3);
lean_ctor_set(x_87, 0, x_5);
lean_ctor_set(x_87, 1, x_6);
lean_ctor_set(x_87, 2, x_7);
lean_ctor_set(x_87, 3, x_8);
lean_ctor_set(x_87, 4, x_9);
lean_ctor_set(x_87, 5, x_10);
lean_ctor_set(x_87, 6, x_11);
lean_ctor_set(x_87, 7, x_12);
lean_ctor_set(x_87, 8, x_26);
lean_ctor_set(x_87, 9, x_14);
lean_ctor_set(x_87, 10, x_15);
lean_ctor_set(x_87, 11, x_16);
lean_ctor_set(x_87, 12, x_20);
lean_ctor_set(x_87, 13, x_21);
lean_ctor_set_uint8(x_87, sizeof(void*)*14, x_17);
lean_ctor_set_uint8(x_87, sizeof(void*)*14 + 1, x_18);
lean_ctor_set_uint8(x_87, sizeof(void*)*14 + 2, x_19);
x_30 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_31; uint8_t x_32; 
x_31 = ((lean_object*)(l_Lake_configFileExists___closed__0));
x_32 = lean_string_dec_eq(x_25, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = ((lean_object*)(l_Lake_configFileExists___closed__1));
x_34 = lean_string_dec_eq(x_25, x_33);
lean_dec(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_30);
x_35 = ((lean_object*)(l_Lake_loadPackageCore___closed__0));
x_36 = lean_string_append(x_1, x_35);
x_37 = lean_string_append(x_36, x_26);
lean_dec_ref(x_26);
x_38 = 3;
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_38);
x_40 = lean_array_get_size(x_3);
x_41 = lean_array_push(x_3, x_39);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
lean_object* x_43; 
lean_dec_ref(x_26);
lean_dec_ref(x_1);
x_43 = l_Lake_loadTomlConfig(x_30, x_3);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_54; 
x_44 = lean_ctor_get(x_43, 0);
x_45 = lean_ctor_get(x_43, 1);
x_54 = !lean_is_exclusive(x_43);
if (x_54 == 0)
{
x_46 = x_43;
x_47 = x_54;
goto block_53;
}
else
{
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_43);
x_46 = lean_box(0);
x_47 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_48);
if (x_47 == 0)
{
lean_ctor_set(x_46, 0, x_49);
x_50 = x_46;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_45);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_63; 
x_55 = lean_ctor_get(x_43, 0);
x_56 = lean_ctor_get(x_43, 1);
x_63 = !lean_is_exclusive(x_43);
if (x_63 == 0)
{
x_57 = x_43;
x_58 = x_63;
goto block_62;
}
else
{
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_43);
x_57 = lean_box(0);
x_58 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_59; 
if (x_58 == 0)
{
x_59 = x_57;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_56);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
}
else
{
lean_object* x_64; 
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_64 = l_Lake_loadLeanConfig(x_30, x_3);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_76; 
x_65 = lean_ctor_get(x_64, 0);
x_66 = lean_ctor_get(x_64, 1);
x_76 = !lean_is_exclusive(x_64);
if (x_76 == 0)
{
x_67 = x_64;
x_68 = x_76;
goto block_75;
}
else
{
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_64);
x_67 = lean_box(0);
x_68 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = ((lean_object*)(l_Lake_loadPackageCore___closed__1));
x_70 = ((lean_object*)(l_Lake_loadPackageCore___closed__2));
x_71 = l_Prod_map___redArg(x_69, x_70, x_65);
if (x_68 == 0)
{
lean_ctor_set(x_67, 0, x_71);
x_72 = x_67;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_66);
x_72 = x_74;
goto block_73;
}
block_73:
{
return x_72;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
x_77 = lean_ctor_get(x_64, 0);
x_78 = lean_ctor_get(x_64, 1);
x_85 = !lean_is_exclusive(x_64);
if (x_85 == 0)
{
x_79 = x_64;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_64);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_77);
lean_ctor_set(x_83, 1, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec_ref(x_26);
lean_dec(x_25);
lean_del_object(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_88 = ((lean_object*)(l_Lake_loadPackageCore___closed__3));
x_89 = lean_string_append(x_1, x_88);
x_90 = lean_string_append(x_89, x_13);
lean_dec_ref(x_13);
x_91 = 3;
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_91);
x_93 = lean_array_get_size(x_3);
x_94 = lean_array_push(x_3, x_92);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
lean_dec(x_24);
lean_dec_ref(x_13);
x_96 = ((lean_object*)(l_Lake_configFileExists___closed__0));
lean_inc_ref(x_12);
x_97 = l_System_FilePath_addExtension(x_12, x_96);
lean_inc_ref(x_97);
lean_inc_ref(x_11);
x_98 = l_Lake_joinRelative(x_11, x_97);
lean_inc_ref(x_98);
x_99 = l_Lake_resolvePath(x_98);
x_100 = ((lean_object*)(l_Lake_configFileExists___closed__1));
x_101 = l_System_FilePath_addExtension(x_12, x_100);
lean_inc_ref(x_101);
lean_inc_ref(x_11);
x_102 = l_Lake_joinRelative(x_11, x_101);
x_103 = lean_string_utf8_byte_size(x_99);
x_104 = lean_unsigned_to_nat(0u);
x_105 = lean_nat_dec_eq(x_103, x_104);
if (x_105 == 0)
{
uint8_t x_106; lean_object* x_107; 
lean_dec_ref(x_98);
x_106 = l_System_FilePath_pathExists(x_102);
lean_dec_ref(x_102);
if (x_106 == 0)
{
lean_dec_ref(x_101);
lean_dec_ref(x_1);
x_107 = x_3;
goto block_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; 
x_141 = ((lean_object*)(l_Lake_loadPackageCore___closed__4));
x_142 = lean_string_append(x_1, x_141);
x_143 = lean_string_append(x_142, x_97);
x_144 = ((lean_object*)(l_Lake_loadPackageCore___closed__5));
x_145 = lean_string_append(x_143, x_144);
x_146 = lean_string_append(x_145, x_101);
lean_dec_ref(x_101);
x_147 = ((lean_object*)(l_Lake_loadPackageCore___closed__6));
x_148 = lean_string_append(x_146, x_147);
x_149 = lean_string_append(x_148, x_97);
x_150 = 1;
x_151 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_150);
x_152 = lean_array_push(x_3, x_151);
x_107 = x_152;
goto block_140;
}
block_140:
{
lean_object* x_108; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 8, x_99);
lean_ctor_set(x_22, 7, x_97);
x_108 = x_22;
goto block_138;
}
else
{
lean_object* x_139; 
x_139 = lean_alloc_ctor(0, 14, 3);
lean_ctor_set(x_139, 0, x_5);
lean_ctor_set(x_139, 1, x_6);
lean_ctor_set(x_139, 2, x_7);
lean_ctor_set(x_139, 3, x_8);
lean_ctor_set(x_139, 4, x_9);
lean_ctor_set(x_139, 5, x_10);
lean_ctor_set(x_139, 6, x_11);
lean_ctor_set(x_139, 7, x_97);
lean_ctor_set(x_139, 8, x_99);
lean_ctor_set(x_139, 9, x_14);
lean_ctor_set(x_139, 10, x_15);
lean_ctor_set(x_139, 11, x_16);
lean_ctor_set(x_139, 12, x_20);
lean_ctor_set(x_139, 13, x_21);
lean_ctor_set_uint8(x_139, sizeof(void*)*14, x_17);
lean_ctor_set_uint8(x_139, sizeof(void*)*14 + 1, x_18);
lean_ctor_set_uint8(x_139, sizeof(void*)*14 + 2, x_19);
x_108 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_109; 
x_109 = l_Lake_loadLeanConfig(x_108, x_107);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_128; 
x_110 = lean_ctor_get(x_109, 0);
x_111 = lean_ctor_get(x_109, 1);
x_128 = !lean_is_exclusive(x_109);
if (x_128 == 0)
{
x_112 = x_109;
x_113 = x_128;
goto block_127;
}
else
{
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_109);
x_112 = lean_box(0);
x_113 = x_128;
goto block_127;
}
block_127:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_126; 
x_114 = lean_ctor_get(x_110, 0);
x_115 = lean_ctor_get(x_110, 1);
x_126 = !lean_is_exclusive(x_110);
if (x_126 == 0)
{
x_116 = x_110;
x_117 = x_126;
goto block_125;
}
else
{
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_110);
x_116 = lean_box(0);
x_117 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_115);
if (x_117 == 0)
{
lean_ctor_set(x_116, 1, x_118);
x_119 = x_116;
goto block_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_114);
lean_ctor_set(x_124, 1, x_118);
x_119 = x_124;
goto block_123;
}
block_123:
{
lean_object* x_120; 
if (x_113 == 0)
{
lean_ctor_set(x_112, 0, x_119);
x_120 = x_112;
goto block_121;
}
else
{
lean_object* x_122; 
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_111);
x_120 = x_122;
goto block_121;
}
block_121:
{
return x_120;
}
}
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_137; 
x_129 = lean_ctor_get(x_109, 0);
x_130 = lean_ctor_get(x_109, 1);
x_137 = !lean_is_exclusive(x_109);
if (x_137 == 0)
{
x_131 = x_109;
x_132 = x_137;
goto block_136;
}
else
{
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_109);
x_131 = lean_box(0);
x_132 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_133; 
if (x_132 == 0)
{
x_133 = x_131;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_129);
lean_ctor_set(x_135, 1, x_130);
x_133 = x_135;
goto block_134;
}
block_134:
{
return x_133;
}
}
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; 
lean_dec_ref(x_99);
lean_dec_ref(x_97);
lean_inc_ref(x_102);
x_153 = l_Lake_resolvePath(x_102);
x_154 = lean_string_utf8_byte_size(x_153);
x_155 = lean_nat_dec_eq(x_154, x_104);
if (x_155 == 0)
{
lean_object* x_156; 
lean_dec_ref(x_102);
lean_dec_ref(x_98);
lean_dec_ref(x_1);
if (x_23 == 0)
{
lean_ctor_set(x_22, 8, x_153);
lean_ctor_set(x_22, 7, x_101);
x_156 = x_22;
goto block_178;
}
else
{
lean_object* x_179; 
x_179 = lean_alloc_ctor(0, 14, 3);
lean_ctor_set(x_179, 0, x_5);
lean_ctor_set(x_179, 1, x_6);
lean_ctor_set(x_179, 2, x_7);
lean_ctor_set(x_179, 3, x_8);
lean_ctor_set(x_179, 4, x_9);
lean_ctor_set(x_179, 5, x_10);
lean_ctor_set(x_179, 6, x_11);
lean_ctor_set(x_179, 7, x_101);
lean_ctor_set(x_179, 8, x_153);
lean_ctor_set(x_179, 9, x_14);
lean_ctor_set(x_179, 10, x_15);
lean_ctor_set(x_179, 11, x_16);
lean_ctor_set(x_179, 12, x_20);
lean_ctor_set(x_179, 13, x_21);
lean_ctor_set_uint8(x_179, sizeof(void*)*14, x_17);
lean_ctor_set_uint8(x_179, sizeof(void*)*14 + 1, x_18);
lean_ctor_set_uint8(x_179, sizeof(void*)*14 + 2, x_19);
x_156 = x_179;
goto block_178;
}
block_178:
{
lean_object* x_157; 
x_157 = l_Lake_loadTomlConfig(x_156, x_3);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; uint8_t x_168; 
x_158 = lean_ctor_get(x_157, 0);
x_159 = lean_ctor_get(x_157, 1);
x_168 = !lean_is_exclusive(x_157);
if (x_168 == 0)
{
x_160 = x_157;
x_161 = x_168;
goto block_167;
}
else
{
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_157);
x_160 = lean_box(0);
x_161 = x_168;
goto block_167;
}
block_167:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_box(0);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_158);
lean_ctor_set(x_163, 1, x_162);
if (x_161 == 0)
{
lean_ctor_set(x_160, 0, x_163);
x_164 = x_160;
goto block_165;
}
else
{
lean_object* x_166; 
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_159);
x_164 = x_166;
goto block_165;
}
block_165:
{
return x_164;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; uint8_t x_177; 
x_169 = lean_ctor_get(x_157, 0);
x_170 = lean_ctor_get(x_157, 1);
x_177 = !lean_is_exclusive(x_157);
if (x_177 == 0)
{
x_171 = x_157;
x_172 = x_177;
goto block_176;
}
else
{
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_157);
x_171 = lean_box(0);
x_172 = x_177;
goto block_176;
}
block_176:
{
lean_object* x_173; 
if (x_172 == 0)
{
x_173 = x_171;
goto block_174;
}
else
{
lean_object* x_175; 
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_169);
lean_ctor_set(x_175, 1, x_170);
x_173 = x_175;
goto block_174;
}
block_174:
{
return x_173;
}
}
}
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec_ref(x_153);
lean_dec_ref(x_101);
lean_del_object(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_180 = ((lean_object*)(l_Lake_loadPackageCore___closed__7));
x_181 = lean_string_append(x_1, x_180);
x_182 = lean_string_append(x_181, x_98);
lean_dec_ref(x_98);
x_183 = ((lean_object*)(l_Lake_loadPackageCore___closed__8));
x_184 = lean_string_append(x_182, x_183);
x_185 = lean_string_append(x_184, x_102);
lean_dec_ref(x_102);
x_186 = 3;
x_187 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set_uint8(x_187, sizeof(void*)*1, x_186);
x_188 = lean_array_get_size(x_3);
x_189 = lean_array_push(x_3, x_187);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_loadPackageCore(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_searchPathRef;
x_6 = l_Lake_Env_leanSearchPath(x_4);
x_7 = lean_st_ref_set(x_5, x_6);
x_8 = ((lean_object*)(l_Lake_loadPackage___closed__0));
x_9 = l_Lake_loadPackageCore(x_8, x_1, x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_19; 
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_9, 1);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
x_12 = x_9;
x_13 = x_19;
goto block_18;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_14);
x_15 = x_12;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_11);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
x_28 = !lean_is_exclusive(x_9);
if (x_28 == 0)
{
x_22 = x_9;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_loadPackage(x_1, x_2);
return x_4;
}
}
lean_object* runtime_initialize_Lake_Load_Config(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Package(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Lean(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Toml(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Load_Package(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Load_Config(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Package(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_IO(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Lean(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Toml(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Load_Package(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Load_Config(uint8_t builtin);
lean_object* initialize_Lake_Config_Package(uint8_t builtin);
lean_object* initialize_Lake_Util_IO(uint8_t builtin);
lean_object* initialize_Lake_Load_Lean(uint8_t builtin);
lean_object* initialize_Lake_Load_Toml(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Package(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Load_Config(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Package(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Lean(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Toml(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Package(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Load_Package(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Load_Package(builtin);
}
#ifdef __cplusplus
}
#endif

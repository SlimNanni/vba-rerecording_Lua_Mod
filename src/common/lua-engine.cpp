#include <cstdio>
#include <cstdlib>
#include <malloc.h>
#include <string>
#include <cassert>
#include <cctype>
#include <cmath>
#include <ctime>

#include <vector>
#include <map>
#include <string>
#include <algorithm>

using namespace std;

#ifdef __linux
	#include <unistd.h> // for unlink
	#include <sys/types.h>
	#include <sys/wait.h>
#endif
#if (defined(WIN32) && !defined(SDL))
	#include <direct.h>
	#include "../win32/stdafx.h"
	#include "../win32/Input.h"
	#include "../win32/MainWnd.h"
	#include "../win32/VBA.h"            // for theApp
	extern "C" {
    extern void systemSetThrottle(int percent);
}
	#include "../win32/Dialogs/LuaOpenDialog.h"
#else
	#define stricmp strcasecmp
	#define strnicmp strncasecmp
#endif

#include "../Port.h"
#include "System.h"
#include "movie.h"
#include "../common/SystemGlobals.h"
#include "../gba/GBA.h"
#include "../gba/GBAinline.h"
#include "../gba/GBAGlobals.h"
#include "../gb/GB.h"
#include "../gb/gbGlobals.h"
#include "../gba/GBASound.h"

#ifdef _WIN32
#include "../win32/Sound.h"
//#include "../win32/WinMiscUtil.h"
extern CString winGetSavestateFilename(const CString &LogicalRomName, int nID);
#else
#endif

bool DemandLua()
{
#ifdef _WIN32
	HMODULE mod = LoadLibrary("lua51.dll");
	if(!mod)
	{
		MessageBox(NULL, "lua51.dll was not found. Please get it into your PATH or in the same directory as VBA.exe", "VBA", MB_OK | MB_ICONERROR);
		return false;
	}
	FreeLibrary(mod);
	return true;
#else
	return true;
#endif
}

extern "C"
{
#include "../lua/src/lua.h"
#include "../lua/src/lauxlib.h"
#include "../lua/src/lualib.h"
#include "../lua/src/lstate.h"
}
#include "vbalua.h"

#include "../SFMT/SFMT.c"

static void (*info_print)(int uid, const char *str);
static void (*info_onstart)(int uid);
static void (*info_onstop)(int uid);
static int	info_uid;

#ifndef countof
	#define countof(a)  (sizeof(a) / sizeof(a[0]))
#endif

static lua_State *LUA;

// Are we running any code right now?
static char *luaScriptName = NULL;

// Are we running any code right now?
static bool8 luaRunning = false;

// True at the frame boundary, false otherwise.
static bool8 frameBoundary = false;

// The execution speed we're running at.
static enum { SPEED_NORMAL, SPEED_NOTHROTTLE, SPEED_TURBO, SPEED_MAXIMUM } speedmode = SPEED_NORMAL;

// Rerecord count skip mode
static bool8 skipRerecords = false;

// Used by the registry to find our functions
static const char *frameAdvanceThread = "VBA.FrameAdvance";
static const char *guiCallbackTable	  = "VBA.GUI";

// True if there's a thread waiting to run after a run of frame-advance.
static bool8 frameAdvanceWaiting = false;

// We save our pause status in the case of a natural death.
//static bool8 wasPaused = false;

// Transparency strength. 255=opaque, 0=so transparent it's invisible
static int transparencyModifier = 255;

// Our joypads.
static uint16 lua_joypads[4];
static uint8  lua_joypads_used = 0;

static bool8  gui_used = false;
static uint8 *gui_data = NULL;		  // BGRA

// Remap input display
struct LuaInputDisplayRemap
{
	uint32 from;
	uint32 to[10];
};
static LuaInputDisplayRemap lua_input_display_remap[4], lua_next_input_display_remap[4];

// Protects Lua calls from going nuts.
// We set this to a big number like 1000 and decrement it
// over time. The script gets knifed once this reaches zero.
static int numTries;

// number of registered memory functions (1 per hooked byte)
static unsigned int numMemHooks;

// Look in inputglobal.h for macros named like BUTTON_MASK_UP to determine the order.
static const char *button_mappings[] = {
	"A", "B", "select", "start", "right", "left", "up", "down", "R", "L"
};

#ifdef _MSC_VER
	#define snprintf _snprintf
	#define vscprintf _vscprintf
#else
	#define stricmp strcasecmp
	#define strnicmp strncasecmp
	#define __forceinline __attribute__((always_inline))
#endif

static const char *luaCallIDStrings[] =
{
	"CALL_BEFOREEMULATION",
	"CALL_AFTEREMULATION",
	"CALL_BEFOREEXIT",
	"CALL_AFTERPOWERON",
	"CALL_BEFOREPOWEROFF",
	"CALL_BEFORESTATELOAD",
	"CALL_AFTERSTATELOAD",
	"CALL_BEFORESTATESAVE",
	"CALL_AFTERSTATESAVE",
};

//make sure we have the right number of strings
CTASSERT(sizeof(luaCallIDStrings) / sizeof(*luaCallIDStrings) == LUACALL_COUNT)

static const char *luaMemHookTypeStrings [] =
{
	"MEMHOOK_WRITE",
	"MEMHOOK_READ",
	"MEMHOOK_EXEC",

	"MEMHOOK_WRITE_SUB",
	"MEMHOOK_READ_SUB",
	"MEMHOOK_EXEC_SUB",
};

//make sure we have the right number of strings
CTASSERT(sizeof(luaMemHookTypeStrings) / sizeof(*luaMemHookTypeStrings) ==  LUAMEMHOOK_COUNT)

static const char* luaJoypadTypeStrings[] =
{
	"JOYPAD_USER",
	"JOYPAD_PLAYBACK",
	"JOYPAD_RECORD",
	"JOYPAD_LUA",
	"JOYPAD_GAME",
};

//make sure we have the right number of strings
CTASSERT(sizeof(luaJoypadTypeStrings) / sizeof(*luaJoypadTypeStrings) == LUAJOYPAD_COUNT)

static char *rawToCString(lua_State * L, int idx = 0);
static const char *toCString(lua_State *L, int idx = 0);

typedef void (*GetColorFunc)(const uint8 *, uint8 *, uint8 *, uint8 *);
typedef void (*SetColorFunc)(uint8 *, uint8, uint8, uint8);

static void getColor16(const uint8 *s, uint8 *r, uint8 *g, uint8 *b)
{
	u16 v = *(const uint16 *)s;
	*r = ((v >> systemBlueShift) & 0x001f) << 3;
	*g = ((v >> systemGreenShift) & 0x001f) << 3;
	*b = ((v >> systemRedShift) & 0x001f) << 3;
}

static void getColor24(const uint8 *s, uint8 *r, uint8 *g, uint8 *b)
{
	if (systemRedShift > systemBlueShift)
		*b = s[0], *g = s[1], *r = s[2];
	else
		*r = s[0], *g = s[1], *b = s[2];
}

static void getColor32(const uint8 *s, uint8 *r, uint8 *g, uint8 *b)
{
	u32 v = *(const uint32 *)s;
	*b = ((v >> systemBlueShift) & 0x001f) << 3;
	*g = ((v >> systemGreenShift) & 0x001f) << 3;
	*r = ((v >> systemRedShift) & 0x001f) << 3;
}

static void setColor16(uint8 *s, uint8 r, uint8 g, uint8 b)
{
	*(uint16 *)s = ((b >> 3) & 0x01f) <<
				   systemBlueShift |
				   ((g >> 3) & 0x01f) <<
				   systemGreenShift |
				   ((r >> 3) & 0x01f) <<
				   systemRedShift;
}

static void setColor24(uint8 *s, uint8 r, uint8 g, uint8 b)
{
	if (systemRedShift > systemBlueShift)
		s[0] = b, s[1] = g, s[2] = r;
	else
		s[0] = r, s[1] = g, s[2] = b;
}

static void setColor32(uint8 *s, uint8 r, uint8 g, uint8 b)
{
	*(uint32 *)s = ((b >> 3) & 0x01f) <<
				   systemBlueShift |
				   ((g >> 3) & 0x01f) <<
				   systemGreenShift |
				   ((r >> 3) & 0x01f) <<
				   systemRedShift;
}

static bool getColorIOFunc(int depth, GetColorFunc *getColor, SetColorFunc *setColor)
{
	switch (depth)
	{
	case 16:
		if (getColor)
			*getColor = getColor16;
		if (setColor)
			*setColor = setColor16;
		return true;
	case 24:
		if (getColor)
			*getColor = getColor24;
		if (setColor)
			*setColor = setColor24;
		return true;
	case 32:
		if (getColor)
			*getColor = getColor32;
		if (setColor)
			*setColor = setColor32;
		return true;
	default:
		return false;
	}
}

/**
 * Resets emulator speed / pause states after script exit.
 */
static void VBALuaOnStop(void)
{
	luaRunning		 = false;
	lua_joypads_used = 0;
	gui_used		 = false;
	for (int i = 0; i < 4; ++i)
	{
		lua_input_display_remap[i].from = 0;
		lua_next_input_display_remap[i].from = 0;
	}
	//if (wasPaused)
	//	systemSetPause(true);
}

/**
 * Asks Lua if it wants control of the emulator's speed.
 * Returns 0 if no, 1 if yes. If yes, we also tamper with the
 * IPPU's settings for speed ourselves, so the calling code
 * need not do anything.
 */
int VBALuaSpeed(void)
{
	if (!LUA || !luaRunning)
		return 0;

	//printf("%d\n", speedmode);
	switch (speedmode)
	{
	/*
	case SPEED_NORMAL:
		return 0;
	case SPEED_NOTHROTTLE:
		IPPU.RenderThisFrame = true;
		return 1;

	case SPEED_TURBO:
		IPPU.SkippedFrames++;
		if (IPPU.SkippedFrames >= 40) {
			IPPU.SkippedFrames = 0;
			IPPU.RenderThisFrame = true;
		}
		else
			IPPU.RenderThisFrame = false;
		return 1;

	// In mode 3, SkippedFrames is set to zero so that the frame
	// skipping code doesn't try anything funny.
	case SPEED_MAXIMUM:
		IPPU.SkippedFrames=0;
		IPPU.RenderThisFrame = false;
		return 1;
	 */
	case 0: // FIXME: to get rid of the warning
	default:
		assert(false);
		return 0;
	}
}

///////////////////////////
// vba.speedmode(string mode)
//
//   Takes control of the emulation speed
//   of the system. Normal is normal speed (60fps, 50 for PAL),
//   nothrottle disables speed control but renders every frame,
//   turbo renders only a few frames in order to speed up emulation,

//   maximum renders no frames
static int vba_speedmode(lua_State *L)
{
	const char *mode = luaL_checkstring(L, 1);

	if (strcasecmp(mode, "normal") == 0)
	{
		speedmode = SPEED_NORMAL;
	}
	else if (strcasecmp(mode, "nothrottle") == 0)
	{
		speedmode = SPEED_NOTHROTTLE;
	}
	else if (strcasecmp(mode, "turbo") == 0)
	{
		speedmode = SPEED_TURBO;
	}
	else if (strcasecmp(mode, "maximum") == 0)
	{
		speedmode = SPEED_MAXIMUM;
	}
	else
		luaL_error(L, "Invalid mode %s to vba.speedmode", mode);

	//printf("new speed mode:  %d\n", speedmode);
	return 0;
}

// vba.frameadvnace()
//
//  Executes a frame advance. Occurs by yielding the coroutine, then re-running

//  when we break out.
static int vba_frameadvance(lua_State *L)
{
	// We're going to sleep for a frame-advance. Take notes.
	if (frameAdvanceWaiting)
		return luaL_error(L, "can't call vba.frameadvance() from here");

	frameAdvanceWaiting = true;

	// Don't do this! The user won't like us sending their emulator out of control!
	//	Settings.FrameAdvance = true;
	// Now we can yield to the main
	return lua_yield(L, 0);

	// It's actually rather disappointing...
}

// vba.pause()
//
//  Pauses the emulator, function "waits" until the user unpauses.
//  This function MAY be called from a non-frame boundary, but the frame

//  finishes executing anwyays. In this case, the function returns immediately.
static int vba_pause(lua_State *L)
{
	systemSetPause(true);
	speedmode = SPEED_NORMAL;

	// Return control if we're midway through a frame. We can't pause here.
	if (frameAdvanceWaiting)
	{
		return 0;
	}

	// If it's on a frame boundary, we also yield.
	frameAdvanceWaiting = true;
	return lua_yield(L, 0);
}

static int vba_registerpoweron(lua_State *L)
{
	if (!lua_isnil(L, 1))
		luaL_checktype(L, 1, LUA_TFUNCTION);
	lua_settop(L, 1);
	lua_getfield(L, LUA_REGISTRYINDEX, luaCallIDStrings[LUACALL_AFTERPOWERON]);
	lua_insert(L, 1);
	lua_setfield(L, LUA_REGISTRYINDEX, luaCallIDStrings[LUACALL_AFTERPOWERON]);

	//StopScriptIfFinished(luaStateToUIDMap[L]);
	return 1;
}

static int vba_registerpoweroff(lua_State *L)
{
	if (!lua_isnil(L, 1))
		luaL_checktype(L, 1, LUA_TFUNCTION);
	lua_settop(L, 1);
	lua_getfield(L, LUA_REGISTRYINDEX, luaCallIDStrings[LUACALL_BEFOREPOWEROFF]);
	lua_insert(L, 1);
	lua_setfield(L, LUA_REGISTRYINDEX, luaCallIDStrings[LUACALL_BEFOREPOWEROFF]);

	//StopScriptIfFinished(luaStateToUIDMap[L]);
	return 1;
}

static int vba_registerloading(lua_State *L)
{
	if (!lua_isnil(L, 1))
		luaL_checktype(L, 1, LUA_TFUNCTION);
	lua_settop(L, 1);
	lua_getfield(L, LUA_REGISTRYINDEX, luaCallIDStrings[LUACALL_BEFORESTATELOAD]);
	lua_insert(L, 1);
	lua_setfield(L, LUA_REGISTRYINDEX, luaCallIDStrings[LUACALL_BEFORESTATELOAD]);

	//StopScriptIfFinished(luaStateToUIDMap[L]);
	return 1;
}

static int vba_registerloaded(lua_State *L)
{
	if (!lua_isnil(L, 1))
		luaL_checktype(L, 1, LUA_TFUNCTION);
	lua_settop(L, 1);
	lua_getfield(L, LUA_REGISTRYINDEX, luaCallIDStrings[LUACALL_AFTERSTATELOAD]);
	lua_insert(L, 1);
	lua_setfield(L, LUA_REGISTRYINDEX, luaCallIDStrings[LUACALL_AFTERSTATELOAD]);

	//StopScriptIfFinished(luaStateToUIDMap[L]);
	return 1;
}

static int vba_registersaving(lua_State *L)
{
	if (!lua_isnil(L, 1))
		luaL_checktype(L, 1, LUA_TFUNCTION);
	lua_settop(L, 1);
	lua_getfield(L, LUA_REGISTRYINDEX, luaCallIDStrings[LUACALL_BEFORESTATESAVE]);
	lua_insert(L, 1);
	lua_setfield(L, LUA_REGISTRYINDEX, luaCallIDStrings[LUACALL_BEFORESTATESAVE]);

	//StopScriptIfFinished(luaStateToUIDMap[L]);
	return 1;
}

static int vba_registersaved(lua_State *L)
{
	if (!lua_isnil(L, 1))
		luaL_checktype(L, 1, LUA_TFUNCTION);
	lua_settop(L, 1);
	lua_getfield(L, LUA_REGISTRYINDEX, luaCallIDStrings[LUACALL_AFTERSTATESAVE]);
	lua_insert(L, 1);
	lua_setfield(L, LUA_REGISTRYINDEX, luaCallIDStrings[LUACALL_AFTERSTATESAVE]);

	//StopScriptIfFinished(luaStateToUIDMap[L]);
	return 1;
}

static int vba_registerbefore(lua_State *L)
{
	if (!lua_isnil(L, 1))
		luaL_checktype(L, 1, LUA_TFUNCTION);
	lua_settop(L, 1);
	lua_getfield(L, LUA_REGISTRYINDEX, luaCallIDStrings[LUACALL_BEFOREEMULATION]);
	lua_insert(L, 1);
	lua_setfield(L, LUA_REGISTRYINDEX, luaCallIDStrings[LUACALL_BEFOREEMULATION]);

	//StopScriptIfFinished(luaStateToUIDMap[L]);
	return 1;
}

static int vba_registerafter(lua_State *L)
{
	if (!lua_isnil(L, 1))
		luaL_checktype(L, 1, LUA_TFUNCTION);
	lua_settop(L, 1);
	lua_getfield(L, LUA_REGISTRYINDEX, luaCallIDStrings[LUACALL_AFTEREMULATION]);
	lua_insert(L, 1);
	lua_setfield(L, LUA_REGISTRYINDEX, luaCallIDStrings[LUACALL_AFTEREMULATION]);

	//StopScriptIfFinished(luaStateToUIDMap[L]);
	return 1;
}

static int vba_registerexit(lua_State *L)
{
	if (!lua_isnil(L, 1))
		luaL_checktype(L, 1, LUA_TFUNCTION);
	lua_settop(L, 1);
	lua_getfield(L, LUA_REGISTRYINDEX, luaCallIDStrings[LUACALL_BEFOREEXIT]);
	lua_insert(L, 1);
	lua_setfield(L, LUA_REGISTRYINDEX, luaCallIDStrings[LUACALL_BEFOREEXIT]);

	//StopScriptIfFinished(luaStateToUIDMap[L]);
	return 1;
}

static inline bool isalphaorunderscore(char c)
{
	return isalpha(c) || c == '_';
}

static std::vector<const void *> s_tableAddressStack; // prevents infinite recursion of a table within a table (when cycle is
													  // found, print something like table:parent)
static std::vector<const void *> s_metacallStack; // prevents infinite recursion if something's __tostring returns another table
												  // that contains that something (when cycle is found, print the inner result
												  // without using __tostring)

#define APPENDSPRINT(...) { \
	int _n = snprintf(ptr, remaining, __VA_ARGS__); \
	if (_n >= 0) { ptr += _n; remaining -= _n; } \
	else { remaining = 0; } \
	}
static void toCStringConverter(lua_State *L, int i, char * &ptr, int &remaining)
{
	if (remaining <= 0)
		return;

	const char *str = ptr; // for debugging

	// if there is a __tostring metamethod then call it
	int usedMeta = luaL_callmeta(L, i, "__tostring");
	if (usedMeta)
	{
		std::vector<const void *>::const_iterator foundCycleIter = std::find(s_metacallStack.begin(), s_metacallStack.end(), lua_topointer(L, i));
		if (foundCycleIter != s_metacallStack.end())
		{
			lua_pop(L, 1);
			usedMeta = false;
		}
		else
		{
			s_metacallStack.push_back(lua_topointer(L, i));
			i = lua_gettop(L);
		}
	}

	switch (lua_type(L, i))
	{
	case LUA_TNONE:
		break;
	case LUA_TNIL:
		APPENDSPRINT("nil") break;
	case LUA_TBOOLEAN:
		APPENDSPRINT(lua_toboolean(L, i) ? "true" : "false") break;
	case LUA_TSTRING:
		APPENDSPRINT("%s", lua_tostring(L, i)) break;
	case LUA_TNUMBER:
		APPENDSPRINT("%.12Lg", lua_tonumber(L, i)) break;
	case LUA_TFUNCTION:
		if ((L->base + i - 1)->value.gc->cl.c.isC)
		{
			//lua_CFunction func = lua_tocfunction(L, i);
			//std::map<lua_CFunction, const char*>::iterator iter = s_cFuncInfoMap.find(func);
			//if(iter == s_cFuncInfoMap.end())
			goto defcase;
			//APPENDSPRINT("function(%s)", iter->second)
		}
		else
		{
			APPENDSPRINT("function(")
			Proto * p = (L->base + i - 1)->value.gc->cl.l.p;
			int numParams = p->numparams + (p->is_vararg ? 1 : 0);
			for (int n = 0; n < p->numparams; n++)
			{
				APPENDSPRINT("%s", getstr(p->locvars[n].varname))
				if (n != numParams - 1)
					APPENDSPRINT(",")
			}
			if (p->is_vararg)
				APPENDSPRINT("...")
				APPENDSPRINT(")")
		}
		break;
defcase: default:
		APPENDSPRINT("%s:%p", luaL_typename(L, i), lua_topointer(L, i))
		break;
	case LUA_TTABLE:
		{
			// first make sure there's enough stack space
			if (!lua_checkstack(L, 4))
			{
				// note that even if lua_checkstack never returns false,
				// that doesn't mean we didn't need to call it,
				// because calling it retrieves stack space past LUA_MINSTACK
				goto defcase;
			}

			std::vector<const void *>::const_iterator foundCycleIter =
				std::find(s_tableAddressStack.begin(), s_tableAddressStack.end(), lua_topointer(L, i));
			if (foundCycleIter != s_tableAddressStack.end())
			{
				int parentNum = s_tableAddressStack.end() - foundCycleIter;
				if (parentNum > 1)
					APPENDSPRINT("%s:parent^%d", luaL_typename(L, i), parentNum)
				else
					APPENDSPRINT("%s:parent", luaL_typename(L, i))
			}
			else
			{
				s_tableAddressStack.push_back(lua_topointer(L, i));
				struct Scope { ~Scope(){ s_tableAddressStack.pop_back(); } } scope;

				APPENDSPRINT("{")

				lua_pushnil(L); // first key
				int		   keyIndex = lua_gettop(L);
				int		   valueIndex = keyIndex + 1;
				bool	   first = true;
				bool	   skipKey = true; // true if we're still in the "array part" of the table
				lua_Number arrayIndex = (lua_Number)0;
				while (lua_next(L, i))
				{
					if (first)
						first = false;
					else
						APPENDSPRINT(", ")
					if (skipKey)
					{
						arrayIndex += (lua_Number)1;
						bool keyIsNumber = (lua_type(L, keyIndex) == LUA_TNUMBER);
						skipKey = keyIsNumber && (lua_tonumber(L, keyIndex) == arrayIndex);
					}
					if (!skipKey)
					{
						bool keyIsString = (lua_type(L, keyIndex) == LUA_TSTRING);
						bool invalidLuaIdentifier = (!keyIsString || !isalphaorunderscore(*lua_tostring(L, keyIndex)));
						if (invalidLuaIdentifier)
							if (keyIsString)
								APPENDSPRINT("['")
							else
								APPENDSPRINT("[")

						toCStringConverter(L, keyIndex, ptr, remaining);
						// key

						if (invalidLuaIdentifier)
							if (keyIsString)
								APPENDSPRINT("']=")
							else
								APPENDSPRINT("]=")
						else
							APPENDSPRINT("=")
					}

					bool valueIsString = (lua_type(L, valueIndex) == LUA_TSTRING);
					if (valueIsString)
						APPENDSPRINT("'")

					toCStringConverter(L, valueIndex, ptr, remaining);  // value

					if (valueIsString)
						APPENDSPRINT("'")

					lua_pop(L, 1);

					if (remaining <= 0)
					{
						lua_settop(L, keyIndex - 1); // stack might not be clean yet if we're breaking
													// early
						break;
					}
				}
				APPENDSPRINT("}")
			}
		}
		break;
	}

	if (usedMeta)
	{
		s_metacallStack.pop_back();
		lua_pop(L, 1);
	}
}

static const int s_tempStrMaxLen = 64 * 1024;
static char s_tempStr [s_tempStrMaxLen];

static char *rawToCString(lua_State *L, int idx)
{
	int a = idx > 0 ? idx : 1;
	int n = idx > 0 ? idx : lua_gettop(L);

	char *ptr = s_tempStr;
	*ptr = 0;

	int remaining = s_tempStrMaxLen;
	for (int i = a; i <= n; i++)
	{
		toCStringConverter(L, i, ptr, remaining);
		if (i != n)
			APPENDSPRINT(" ")
	}

	if (remaining < 3)
	{
		while (remaining < 6)
			remaining++, ptr--;
		APPENDSPRINT("...")
	}
	APPENDSPRINT("\r\n")
	// the trailing newline is so print() can avoid having to do wasteful things to print its newline
	// (string copying would be wasteful and calling info.print() twice can be extremely slow)
	// at the cost of functions that don't want the newline needing to trim off the last two characters
	// (which is a very fast operation and thus acceptable in this case)

	return s_tempStr;
}
#undef APPENDSPRINT

// replacement for luaB_tostring() that is able to show the contents of tables (and formats numbers better, and show function
// prototypes)
// can be called directly from lua via tostring(), assuming tostring hasn't been reassigned
static int tostring(lua_State *L)
{
	char *str = rawToCString(L);
	str[strlen(str) - 2] = 0; // hack: trim off the \r\n (which is there to simplify the print function's
								// task)
	lua_pushstring(L, str);
	return 1;
}

// like rawToCString, but will check if the global Lua function tostring()
// has been replaced with a custom function, and call that instead if so
static const char *toCString(lua_State *L, int idx)
{
	int a = idx > 0 ? idx : 1;
	int n = idx > 0 ? idx : lua_gettop(L);
	lua_getglobal(L, "tostring");
	lua_CFunction cf = lua_tocfunction(L, -1);
	if (cf == tostring || lua_isnil(L, -1)) // optimization: if using our own C tostring function, we can
											// bypass the call through Lua and all the string object
											// allocation that would entail
	{
		lua_pop(L, 1);
		return rawToCString(L, idx);
	}
	else // if the user overrided the tostring function, we have to actually call it and store the
		 // temporarily allocated string it returns
	{
		lua_pushstring(L, "");
		for (int i = a; i <= n; i++)
		{
			lua_pushvalue(L, -2); // function to be called
			lua_pushvalue(L, i); // value to print
			lua_call(L, 1, 1);
			if (lua_tostring(L, -1) == NULL)
				luaL_error(L, LUA_QL("tostring") " must return a string to " LUA_QL("print"));
			lua_pushstring(L, (i < n) ? " " : "\r\n");
			lua_concat(L, 3);
		}
		const char *str = lua_tostring(L, -1);
		strncpy(s_tempStr, str, s_tempStrMaxLen);
		s_tempStr[s_tempStrMaxLen - 1] = 0;
		lua_pop(L, 2);
		return s_tempStr;
	}
}

// replacement for luaB_print() that goes to the appropriate textbox instead of stdout
static int print(lua_State *L)
{
	const char *str = toCString(L);

	int uid = info_uid; //luaStateToUIDMap[L->l_G->mainthread];
	//LuaContextInfo& info = GetCurrentInfo();

	if (info_print)
		info_print(uid, str);
	else
		puts(str);

	//worry(L, 100);
	return 0;
}

static int printerror(lua_State *L, int idx)
{
	lua_checkstack(L, lua_gettop(L) + 4);

	if (idx < 0)
		idx = lua_gettop(L) + 1 + idx;

	const char *str = rawToCString(L, idx);

	int uid = info_uid; //luaStateToUIDMap[L->l_G->mainthread];
	//LuaContextInfo& info = GetCurrentInfo();

	if (info_print)
		info_print(uid, str);
	else
		fputs(str, stderr);

	//worry(L, 100);
	return 0;
}

// vba.message(string msg)
//
//  Displays the given message on the screen.
static int vba_message(lua_State *L)
{
	const char *msg = luaL_checkstring(L, 1);
	systemScreenMessage(msg);

	return 0;
}

// provides an easy way to copy a table from Lua
// (simple assignment only makes an alias, but sometimes an independent table is desired)
// currently this function only performs a shallow copy,
// but I think it should be changed to do a deep copy (possibly of configurable depth?)
// that maintains the internal table reference structure
static int copytable(lua_State *L)
{
	int origIndex = 1; // we only care about the first argument
	int origType = lua_type(L, origIndex);
	if (origType == LUA_TNIL)
	{
		lua_pushnil(L);
		return 1;
	}
	if (origType != LUA_TTABLE)
	{
		luaL_typerror(L, 1, lua_typename(L, LUA_TTABLE));
		lua_pushnil(L);
		return 1;
	}

	lua_createtable(L, lua_objlen(L, 1), 0);
	int copyIndex = lua_gettop(L);

	lua_pushnil(L); // first key
	int keyIndex = lua_gettop(L);
	int valueIndex = keyIndex + 1;

	while (lua_next(L, origIndex))
	{
		lua_pushvalue(L, keyIndex);
		lua_pushvalue(L, valueIndex);
		lua_rawset(L, copyIndex); // copytable[key] = value
		lua_pop(L, 1);
	}

	// copy the reference to the metatable as well, if any
	if (lua_getmetatable(L, origIndex))
		lua_setmetatable(L, copyIndex);

	return 1; // return the new table
}

// because print traditionally shows the address of tables,
// and the print function I provide instead shows the contents of tables,
// I also provide this function
// (otherwise there would be no way to see a table's address, AFAICT)
static int addressof(lua_State *L)
{
	const void *ptr = lua_topointer(L, -1);
	lua_pushinteger(L, (lua_Integer)ptr);
	return 1;
}

struct registerPointerMap
{
	const char *  registerName;
	unsigned int *pointer;
	int dataSize;
};

extern gbRegister AF;
extern gbRegister BC;
extern gbRegister DE;
extern gbRegister HL;
extern gbRegister SP;
extern gbRegister PC;
extern u16 IFF;

#define RPM_ENTRY(name, var) \
	{ name, (unsigned int *)&var, sizeof(var) },

registerPointerMap regPointerMap [] = {
	// gba registers
	RPM_ENTRY("r0",	  reg[0].I)
	RPM_ENTRY("r1",	  reg[1].I)
	RPM_ENTRY("r2",	  reg[2].I)
	RPM_ENTRY("r3",	  reg[3].I)
	RPM_ENTRY("r4",	  reg[4].I)
	RPM_ENTRY("r5",	  reg[5].I)
	RPM_ENTRY("r6",	  reg[6].I)
	RPM_ENTRY("r7",	  reg[7].I)
	RPM_ENTRY("r8",	  reg[8].I)
	RPM_ENTRY("r9",	  reg[9].I)
	RPM_ENTRY("r10",  reg[10].I)
	RPM_ENTRY("r11",  reg[11].I)
	RPM_ENTRY("r12",  reg[12].I)
	RPM_ENTRY("r13",  reg[13].I)
	RPM_ENTRY("r14",  reg[14].I)
	RPM_ENTRY("r15",  reg[15].I)
	RPM_ENTRY("cpsr", reg[16].I)
	RPM_ENTRY("spsr", reg[17].I)
	// gb registers
	RPM_ENTRY("a",	  AF.B.B1)
	RPM_ENTRY("f",	  AF.B.B0)
	RPM_ENTRY("b",	  BC.B.B1)
	RPM_ENTRY("c",	  BC.B.B0)
	RPM_ENTRY("d",	  DE.B.B1)
	RPM_ENTRY("e",	  DE.B.B0)
	RPM_ENTRY("h",	  HL.B.B1)
	RPM_ENTRY("l",	  HL.B.B0)
	RPM_ENTRY("af",	  AF.W)
	RPM_ENTRY("bc",	  BC.W)
	RPM_ENTRY("de",	  DE.W)
	RPM_ENTRY("hl",	  HL.W)
	RPM_ENTRY("sp",	  SP.W)
	RPM_ENTRY("pc",	  PC.W)
	{}
};

#undef RPM_ENTRY

struct cpuToRegisterMap
{
	const char *cpuName;
	registerPointerMap *rpmap;
}
cpuToRegisterMaps [] =
{
	{ "", regPointerMap },
};

//DEFINE_LUA_FUNCTION(memory_getregister, "cpu_dot_registername_string")
static int memory_getregister(lua_State *L)
{
	const char *qualifiedRegisterName = luaL_checkstring(L, 1);
	lua_settop(L, 0);
	for (int cpu = 0; cpu < sizeof(cpuToRegisterMaps) / sizeof(*cpuToRegisterMaps); cpu++)
	{
		cpuToRegisterMap ctrm = cpuToRegisterMaps[cpu];
		int cpuNameLen		  = strlen(ctrm.cpuName);
		if (!strnicmp(qualifiedRegisterName, ctrm.cpuName, cpuNameLen))
		{
			qualifiedRegisterName += cpuNameLen;
			for (int reg = 0; ctrm.rpmap[reg].dataSize; reg++)
			{
				registerPointerMap rpm = ctrm.rpmap[reg];
				if (!stricmp(qualifiedRegisterName, rpm.registerName))
				{
					switch (rpm.dataSize)
					{
					default:
					case 1:
						lua_pushinteger(L, *(unsigned char *)rpm.pointer); break;
					case 2:
						lua_pushinteger(L, *(unsigned short *)rpm.pointer); break;
					case 4:
						lua_pushinteger(L, *(unsigned long *)rpm.pointer); break;
					}
					return 1;
				}
			}
			lua_pushnil(L);
			return 1;
		}
	}
	lua_pushnil(L);
	return 1;
}

//DEFINE_LUA_FUNCTION(memory_setregister, "cpu_dot_registername_string,value")
static int memory_setregister(lua_State *L)
{
	const char *  qualifiedRegisterName = luaL_checkstring(L, 1);
	unsigned long value = (unsigned long)(luaL_checkinteger(L, 2));
	lua_settop(L, 0);
	for (int cpu = 0; cpu < sizeof(cpuToRegisterMaps) / sizeof(*cpuToRegisterMaps); cpu++)
	{
		cpuToRegisterMap ctrm = cpuToRegisterMaps[cpu];
		int cpuNameLen		  = strlen(ctrm.cpuName);
		if (!strnicmp(qualifiedRegisterName, ctrm.cpuName, cpuNameLen))
		{
			qualifiedRegisterName += cpuNameLen;
			for (int reg = 0; ctrm.rpmap[reg].dataSize; reg++)
			{
				registerPointerMap rpm = ctrm.rpmap[reg];
				if (!stricmp(qualifiedRegisterName, rpm.registerName))
				{
					switch (rpm.dataSize)
					{
					default:
					case 1:
						*(unsigned char *)rpm.pointer = (unsigned char)(value & 0xFF); break;
					case 2:
						*(unsigned short *)rpm.pointer = (unsigned short)(value & 0xFFFF); break;
					case 4:
						*(unsigned long *)rpm.pointer = value; break;
					}
					return 0;
				}
			}
			return 0;
		}
	}
	return 0;
}

void HandleCallbackError(lua_State *L)
{
	if (L->errfunc || L->errorJmp)
		luaL_error(L, "%s", lua_tostring(L, -1));
	else
	{
		lua_pushnil(LUA);
		lua_setfield(LUA, LUA_REGISTRYINDEX, guiCallbackTable);

		// Error?
//#if (defined(WIN32) && !defined(SDL))
//		info_print(info_uid, lua_tostring(LUA, -1)); //Clear_Sound_Buffer();
// AfxGetApp()->m_pMainWnd->MessageBox(lua_tostring(LUA, -1), "Lua run error", MB_OK | MB_ICONSTOP);
//#else
//		fprintf(stderr, "Lua thread bombed out: %s\n", lua_tostring(LUA, -1));
//#endif
		printerror(LUA, -1);
		VBALuaStop();
	}
}

void CallRegisteredLuaFunctions(LuaCallID calltype)
{
	assert((unsigned int)calltype < (unsigned int)LUACALL_COUNT);

	const char *idstring = luaCallIDStrings[calltype];

	if (!LUA)
		return;

	lua_settop(LUA, 0);
	lua_getfield(LUA, LUA_REGISTRYINDEX, idstring);

	int errorcode = 0;
	if (lua_isfunction(LUA, -1))
	{
		errorcode = lua_pcall(LUA, 0, 0, 0);
		if (errorcode)
			HandleCallbackError(LUA);
	}
	else
	{
		lua_pop(LUA, 1);
	}
}

// the purpose of this structure is to provide a way of
// QUICKLY determining whether a memory address range has a hook associated with it,
// with a bias toward fast rejection because the majority of addresses will not be hooked.
// (it must not use any part of Lua or perform any per-script operations,
//  otherwise it would definitely be too slow.)
// calculating the regions when a hook is added/removed may be slow,
// but this is an intentional tradeoff to obtain a high speed of checking during later execution
struct TieredRegion
{
	template<unsigned int maxGap>
	struct Region
	{
		struct Island
		{
			unsigned int	   start;
			unsigned int	   end;
			__forceinline bool Contains(unsigned int address, int size) const { return address < end && address + size > start; }
		};
		std::vector<Island> islands;

		void Calculate(const std::vector<unsigned int> &bytes)
		{
			islands.clear();

			unsigned int lastEnd = ~0;

			std::vector<unsigned int>::const_iterator iter = bytes.begin();
			std::vector<unsigned int>::const_iterator end  = bytes.end();
			for (; iter != end; ++iter)
			{
				unsigned int addr = *iter;
				if (addr < lastEnd || addr > lastEnd + (long long)maxGap)
				{
					islands.push_back(Island());
					islands.back().start = addr;
				}
				islands.back(). end = addr + 1;
				lastEnd = addr + 1;
			}
		}

		bool Contains(unsigned int address, int size) const
		{
			//for (size_t i = 0, j = islands.size(); i != j; ++i)
			for (size_t i = islands.size(); i--; )
			{
				if (islands[i].Contains(address, size))
					return true;
			}
			return false;
		}
	};

	Region<0xFFFFFFFF> broad;
	Region<0x1000>	   mid;
	Region<0>		   narrow;

	void Calculate(std::vector<unsigned int> &bytes)
	{
		std:: sort(bytes.begin(), bytes.end());

		broad.Calculate(bytes);
		mid.Calculate(bytes);
		narrow.Calculate(bytes);
	}

	TieredRegion()
	{
		std::vector <unsigned int> temp;
		Calculate(temp);
	}

	__forceinline int NotEmpty()
	{
		return broad.islands.size();
	}

	// note: it is illegal to call this if NotEmpty() returns 0
	__forceinline bool Contains(unsigned int address, int size)
	{
		return broad.islands[0].Contains(address, size) &&
				mid.Contains(address, size) &&
				narrow.Contains(address, size);
	}
};

TieredRegion hookedRegions[LUAMEMHOOK_COUNT];

static void CalculateMemHookRegions(LuaMemHookType hookType)
{
	std::vector<unsigned int> hookedBytes;
//	std::map<int, LuaContextInfo*>::iterator iter = luaContextInfo.begin();
//	std::map<int, LuaContextInfo*>::iterator end = luaContextInfo.end();
//	while(iter != end)
//	{
//		LuaContextInfo& info = *iter->second;
		if (/*info.*/ numMemHooks)
		{
			lua_State *L = LUA /*info.L*/;
			if (L)
			{
				lua_settop(L, 0);
				lua_getfield(L, LUA_REGISTRYINDEX, luaMemHookTypeStrings[hookType]);
				lua_pushnil(L);
				while (lua_next(L, -2))
				{
					if (lua_isfunction(L, -1))
					{
						unsigned int addr = lua_tointeger(L, -2);
						hookedBytes.push_back(addr);
					}
					lua_pop(L, 1);
				}
				lua_settop(L, 0);
			}
		}
//		++iter;
//	}
	hookedRegions[hookType].Calculate(hookedBytes);
}

static void CallRegisteredLuaMemHook_LuaMatch(unsigned int address, int size, unsigned int value, LuaMemHookType hookType)
{
//	std::map<int, LuaContextInfo*>::iterator iter = luaContextInfo.begin();
//	std::map<int, LuaContextInfo*>::iterator end = luaContextInfo.end();
//	while(iter != end)
//	{
//		LuaContextInfo& info = *iter->second;
	if (/*info.*/ numMemHooks)
	{
		lua_State *L = LUA /*info.L*/;
		if (L /* && !info.panic*/)
		{
#ifdef USE_INFO_STACK
			infoStack.insert(infoStack.begin(), &info);
			struct Scope { ~Scope(){ infoStack.erase(infoStack.begin()); } } scope;
#endif
			lua_settop(L, 0);
			lua_getfield(L, LUA_REGISTRYINDEX, luaMemHookTypeStrings[hookType]);
			for (int i = address; i != address + size; i++)
			{
				lua_rawgeti(L, -1, i);
				if (lua_isfunction(L, -1))
				{
					bool wasRunning = (luaRunning != 0) /*info.running*/;
					luaRunning /*info.running*/ = true;
					//RefreshScriptSpeedStatus();
					lua_pushinteger(L, address);
					lua_pushinteger(L, size);
					int errorcode = lua_pcall(L, 2, 0, 0);
					luaRunning /*info.running*/ = wasRunning;
					//RefreshScriptSpeedStatus();
					if (errorcode)
					{
						HandleCallbackError(L);
						//int uid = iter->first;
						//HandleCallbackError(L,info,uid,true);
					}
					break;
				}
				else
				{
					lua_pop(L, 1);
				}
			}
			lua_settop(L, 0);
		}
	}
//		++iter;
//	}
}

void CallRegisteredLuaMemHook(unsigned int address, int size, unsigned int value, LuaMemHookType hookType)
{
	// performance critical! (called VERY frequently)
	// I suggest timing a large number of calls to this function in Release if you change anything in here,
	// before and after, because even the most innocent change can make it become 30% to 400% slower.
	// a good amount to test is: 100000000 calls with no hook set, and another 100000000 with a hook set.
	// (on my system that consistently took 200 ms total in the former case and 350 ms total in the latter
	// case)
	if (hookedRegions[hookType].NotEmpty())
	{
		//if((hookType <= LUAMEMHOOK_EXEC) && (address >= 0xE00000))
		//	address |= 0xFF0000; // account for mirroring of RAM
		if (hookedRegions[hookType].Contains(address, size))
			CallRegisteredLuaMemHook_LuaMatch(address, size, value, hookType);  // something has hooked this
																				// specific address
	}
}

static int memory_registerHook(lua_State *L, LuaMemHookType hookType, int defaultSize)
{
	// get first argument: address
	unsigned int addr = luaL_checkinteger(L, 1);
	//if((addr & ~0xFFFFFF) == ~0xFFFFFF)
	//	addr &= 0xFFFFFF;

	// get optional second argument: size
	int size	= defaultSize;
	int funcIdx = 2;
	if (lua_isnumber(L, 2))
	{
		size = luaL_checkinteger(L, 2);
		if (size < 0)
		{
			size  = -size;
			addr -= size;
		}
		funcIdx++;
	}

	// check last argument: callback function
	bool clearing = lua_isnil(L, funcIdx);
	if (!clearing)
		luaL_checktype(L, funcIdx, LUA_TFUNCTION);
	lua_settop(L, funcIdx);

	// get the address-to-callback table for this hook type of the current script
	lua_getfield(L, LUA_REGISTRYINDEX, luaMemHookTypeStrings[hookType]);

	// count how many callback functions we'll be displacing
	int numFuncsAfter  = clearing ? 0 : size;
	int numFuncsBefore = 0;
	for (unsigned int i = addr; i != addr + size; i++)
	{
		lua_rawgeti(L, -1, i);
		if (lua_isfunction(L, -1))
			numFuncsBefore++;
		lua_pop(L, 1);
	}

	// put the callback function in the address slots
	for (unsigned int i = addr; i != addr + size; i++)
	{
		lua_pushvalue(L, -2);
		lua_rawseti(L, -2, i);
	}

	// adjust the count of active hooks
	//LuaContextInfo& info = GetCurrentInfo();
	/*info.*/ numMemHooks += numFuncsAfter - numFuncsBefore;

	// re-cache regions of hooked memory across all scripts
	CalculateMemHookRegions(hookType);

	//StopScriptIfFinished(luaStateToUIDMap[L]);
	return 0;
}

LuaMemHookType MatchHookTypeToCPU(lua_State *L, LuaMemHookType hookType)
{
	int cpuID = 0;

	int cpunameIndex = 0;
	if (lua_type(L, 2) == LUA_TSTRING)
		cpunameIndex = 2;
	else if (lua_type(L, 3) == LUA_TSTRING)
		cpunameIndex = 3;

	if (cpunameIndex)
	{
		const char *cpuName = lua_tostring(L, cpunameIndex);
		if (!stricmp(cpuName, "sub"))
			cpuID = 1;
		lua_remove(L, cpunameIndex);
	}

	switch (cpuID)
	{
	case 0:
		return hookType;

	case 1:
		switch (hookType)
		{
		case LUAMEMHOOK_WRITE:
			return LUAMEMHOOK_WRITE_SUB;
		case LUAMEMHOOK_READ:
			return LUAMEMHOOK_READ_SUB;
		case LUAMEMHOOK_EXEC:
			return LUAMEMHOOK_EXEC_SUB;
		}
	}
	return hookType;
}

static int memory_registerwrite(lua_State *L)
{
	return memory_registerHook(L, MatchHookTypeToCPU(L, LUAMEMHOOK_WRITE), 1);
}

static int memory_registerread(lua_State *L)
{
	return memory_registerHook(L, MatchHookTypeToCPU(L, LUAMEMHOOK_READ), 1);
}

static int memory_registerexec(lua_State *L)
{
	return memory_registerHook(L, MatchHookTypeToCPU(L, LUAMEMHOOK_EXEC), 1);
}

//int vba.lagcount
//

//Returns the lagcounter variable
static int vba_getlagcount(lua_State *L)
{
	lua_pushinteger(L, systemCounters.lagCount);
	return 1;
}

//int vba.lagged
//
//Returns true if the current frame is a lag frame
static int vba_lagged(lua_State *L)
{
	lua_pushboolean(L, systemCounters.laggedLast);
	return 1;
}

// boolean vba.emulating()
int vba_emulating(lua_State *L)
{
	lua_pushboolean(L, systemIsEmulating());
	return 1;
}

int movie_isactive(lua_State *L)
{
	lua_pushboolean(L, VBAMovieIsActive());
	return 1;
}

int movie_isrecording(lua_State *L)
{
	lua_pushboolean(L, VBAMovieIsRecording());
	return 1;
}

int movie_isplaying(lua_State *L)
{
	lua_pushboolean(L, VBAMovieIsPlaying());
	return 1;
}

int movie_getlength(lua_State *L)
{
	if (VBAMovieIsActive())
		lua_pushinteger(L, VBAMovieGetLength());
	else
		lua_pushinteger(L, 0);
	return 1;
}

static int memory_readbyte(lua_State *L)
{
	u32 addr;
	u8	val;

	addr = luaL_checkinteger(L, 1);
	if (systemIsRunningGBA())
	{
		val = CPUReadByteQuick(addr);
	}
	else
	{
		val = gbReadMemoryQuick8(addr);
	}

	lua_pushinteger(L, val);
	return 1;
}

static int memory_readbytesigned(lua_State *L)
{
	u32 addr;
	s8	val;

	addr = luaL_checkinteger(L, 1);
	if (systemIsRunningGBA())
	{
		val = (s8) CPUReadByteQuick(addr);
	}
	else
	{
		val = (s8) gbReadMemoryQuick8(addr);
	}

	lua_pushinteger(L, val);
	return 1;
}

static int memory_readword(lua_State *L)
{
	u32 addr;
	u16 val;

	addr = luaL_checkinteger(L, 1);
	if (systemIsRunningGBA())
	{
		val = CPUReadHalfWordQuick(addr);
	}
	else
	{
		val = gbReadMemoryQuick16(addr & 0x0000FFFF);
	}

	lua_pushinteger(L, val);
	return 1;
}

static int memory_readwordsigned(lua_State *L)
{
	u32 addr;
	s16 val;

	addr = luaL_checkinteger(L, 1);
	if (systemIsRunningGBA())
	{
		val = (s16) CPUReadHalfWordQuick(addr);
	}
	else
	{
		val = (s16) gbReadMemoryQuick16(addr);
	}

	lua_pushinteger(L, val);
	return 1;
}

static int memory_readdword(lua_State *L)
{
	u32 addr;
	u32 val;

	addr = luaL_checkinteger(L, 1);
	if (systemIsRunningGBA())
	{
		val = CPUReadMemoryQuick(addr);
	}
	else
	{
		val = gbReadMemoryQuick32(addr & 0x0000FFFF);
	}

	// lua_pushinteger doesn't work properly for 32bit system, does it?
	if (val >= 0x80000000 && sizeof(int) <= 4)
		lua_pushnumber(L, val);
	else
		lua_pushinteger(L, val);
	return 1;
}

static int memory_readdwordsigned(lua_State *L)
{
	u32 addr;
	s32 val;

	addr = luaL_checkinteger(L, 1);
	if (systemIsRunningGBA())
	{
		val = (s32) CPUReadMemoryQuick(addr);
	}
	else
	{
		val = (s32) gbReadMemoryQuick32(addr);
	}

	lua_pushinteger(L, val);
	return 1;
}

static int memory_readbyterange(lua_State *L)
{
	uint32 address = luaL_checkinteger(L, 1);
	int	   length  = luaL_checkinteger(L, 2);

	if (length < 0)
	{
		address += length;
		length	 = -length;
	}

	// push the array
	lua_createtable(L, abs(length), 0);

	// put all the values into the (1-based) array
	for (int a = address, n = 1; n <= length; a++, n++)
	{
		unsigned char value;

		if (systemIsRunningGBA())
		{
			value = CPUReadByteQuick(a);
		}
		else
		{
			value = gbReadMemoryQuick8(a);
		}

		lua_pushinteger(L, value);
		lua_rawseti(L, -2, n);
	}

	return 1;
}

static int memory_writebyte(lua_State *L)
{
	u32 addr;
	int val;

	addr = luaL_checkinteger(L, 1);
	val	 = luaL_checkinteger(L, 2);
	if (systemIsRunningGBA())
	{
		CPUWriteByteQuick(addr, val);
	}
	else
	{
		gbWriteMemoryQuick8(addr, val);
	}

	CallRegisteredLuaMemHook(addr, 1, val, LUAMEMHOOK_WRITE);
	return 0;
}

static int memory_writeword(lua_State *L)
{
	u32 addr;
	int val;

	addr = luaL_checkinteger(L, 1);
	val	 = luaL_checkinteger(L, 2);
	if (systemIsRunningGBA())
	{
		CPUWriteHalfWordQuick(addr, val);
	}
	else
	{
		gbWriteMemoryQuick16(addr, val);
	}

	CallRegisteredLuaMemHook(addr, 2, val, LUAMEMHOOK_WRITE);
	return 0;
}

static int memory_writedword(lua_State *L)
{
	u32 addr;
	u32 val;

	addr = luaL_checkinteger(L, 1);
	val	 = (s64)luaL_checknumber(L, 2);
	if (systemIsRunningGBA())
	{
		CPUWriteMemoryQuick(addr, val);
	}
	else
	{
		gbWriteMemoryQuick32(addr, val);
	}

	CallRegisteredLuaMemHook(addr, 4, val, LUAMEMHOOK_WRITE);
	return 0;
}

static int memory_gbromreadbyte(lua_State *L)
{
	u32 addr;
	u8	val;

	addr = luaL_checkinteger(L, 1);
	if (systemIsRunningGBA())
	{
		lua_pushnil(L);
		return 1;
	}
	else
	{
		val = gbReadROMQuick8(addr);
	}

	lua_pushinteger(L, val);
	return 1;
}

static int memory_gbromreadbytesigned(lua_State *L)
{
	u32 addr;
	s8	val;

	addr = luaL_checkinteger(L, 1);
	if (systemIsRunningGBA())
	{
		lua_pushnil(L);
		return 1;
	}
	else
	{
		val = (s8) gbReadROMQuick8(addr);
	}

	lua_pushinteger(L, val);
	return 1;
}

static int memory_gbromreadword(lua_State *L)
{
	u32 addr;
	u16 val;

	addr = luaL_checkinteger(L, 1);
	if (systemIsRunningGBA())
	{
		lua_pushnil(L);
		return 1;
	}
	else
	{
		val = gbReadROMQuick16(addr);
	}

	lua_pushinteger(L, val);
	return 1;
}

static int memory_gbromreadwordsigned(lua_State *L)
{
	u32 addr;
	s16 val;

	addr = luaL_checkinteger(L, 1);
	if (systemIsRunningGBA())
	{
		lua_pushnil(L);
		return 1;
	}
	else
	{
		val = (s16) gbReadROMQuick16(addr);
	}

	lua_pushinteger(L, val);
	return 1;
}

static int memory_gbromreaddword(lua_State *L)
{
	u32 addr;
	u32 val;

	addr = luaL_checkinteger(L, 1);
	if (systemIsRunningGBA())
	{
		lua_pushnil(L);
		return 1;
	}
	else
	{
		val = gbReadROMQuick32(addr);
	}

	// lua_pushinteger doesn't work properly for 32bit system, does it?
	if (val >= 0x80000000 && sizeof(int) <= 4)
		lua_pushnumber(L, val);
	else
		lua_pushinteger(L, val);
	return 1;
}

static int memory_gbromreaddwordsigned(lua_State *L)
{
	u32 addr;
	s32 val;

	addr = luaL_checkinteger(L, 1);
	if (systemIsRunningGBA())
	{
		lua_pushnil(L);
		return 1;
	}
	else
	{
		val = (s32) gbReadROMQuick32(addr);
	}

	lua_pushinteger(L, val);
	return 1;
}

static int memory_gbromreadbyterange(lua_State *L)
{
	uint32 address = luaL_checkinteger(L, 1);
	int	   length  = luaL_checkinteger(L, 2);

	if (length < 0)
	{
		address += length;
		length	 = -length;
	}

	// push the array
	lua_createtable(L, abs(length), 0);

	// put all the values into the (1-based) array
	for (int a = address, n = 1; n <= length; a++, n++)
	{
		unsigned char value;

		if (systemIsRunningGBA())
		{
			lua_pushnil(L);
			return 1;
		}
		else
		{
			value = gbReadROMQuick8(a);
		}

		lua_pushinteger(L, value);
		lua_rawseti(L, -2, n);
	}

	return 1;
}

// vba.setthrottle(percent)
static int vba_setthrottle(lua_State* L) {
  int pct = (int)luaL_checkinteger(L, 1);
  if (pct < 6) pct = 6;               // keep within menu's lower bound
  if (pct > 10000) pct = 10000;       // arbitrary high cap
  systemSetThrottle(pct);
  lua_pushinteger(L, pct);
  return 1;
}

// vba.getthrottle() -> percent
static int vba_getthrottle(lua_State* L) {
  lua_pushinteger(L, theApp.throttle);
  return 1;
}

static const struct luaL_reg vbalib[] = {
    //	{"speedmode", vba_speedmode},	// TODO: NYI
    { "frameadvance",	vba_frameadvance	 },
    { "pause",			vba_pause			 },
    { "framecount",		vba_framecount		 },
    { "lagcount",		vba_getlagcount		 },
    { "lagged",			vba_lagged			 },
    { "emulating",		vba_emulating		 },
    { "registerbefore", vba_registerbefore	 },
    { "registerafter",	vba_registerafter	 },
    { "registerexit",	vba_registerexit	 },
    { "registerrun",	vba_registerpoweron	 },
    { "registerclose",	vba_registerpoweroff },
    { "registerloading",vba_registerloading	 },
    { "registerloaded",	vba_registerloaded	 },
    { "registersaving",	vba_registersaving	 },
    { "registersaved",	vba_registersaved	 },
    { "message",		vba_message			 },
    { "remapinputdisplay",	vba_remapinputdisplay	},
    { "setthrottle",	vba_setthrottle		 },
    { "getthrottle",	vba_getthrottle		 },
    { "print",			print				 }, // sure, why not
    { NULL,				NULL				 }
};

static const struct luaL_reg memorylib[] = {
	{ "readbyte",				memory_readbyte				},
	{ "readbytesigned",			memory_readbytesigned		},
	{ "readword",				memory_readword				},
	{ "readwordsigned",			memory_readwordsigned		},
	{ "readdword",				memory_readdword			},
	{ "readdwordsigned",		memory_readdwordsigned		},
	{ "readbyterange",			memory_readbyterange		},
	{ "writebyte",				memory_writebyte			},
	{ "writeword",				memory_writeword			},
	{ "writedword",				memory_writedword			},
	{ "getregister",			memory_getregister			},
	{ "setregister",			memory_setregister			},
	{ "gbromreadbyte",			memory_gbromreadbyte		},
	{ "gbromreadbytesigned",	memory_gbromreadbytesigned	},
	{ "gbromreadword",			memory_gbromreadword		},
	{ "gbromreadwordsigned",	memory_gbromreadwordsigned	},
	{ "gbromreaddword",			memory_gbromreaddword		},
	{ "gbromreaddwordsigned",	memory_gbromreaddwordsigned	},
	{ "gbromreadbyterange",		memory_gbromreadbyterange	},

	// alternate naming scheme for word and double-word and unsigned
	{ "readbyteunsigned",		memory_readbyte				},
	{ "readwordunsigned",		memory_readword				},
	{ "readdwordunsigned",		memory_readdword			},
	{ "readshort",				memory_readword				},
	{ "readshortunsigned",		memory_readword				},
	{ "readshortsigned",		memory_readwordsigned		},
	{ "readlong",				memory_readdword			},
	{ "readlongunsigned",		memory_readdword			},
	{ "readlongsigned",			memory_readdwordsigned		},
	{ "writeshort",				memory_writeword			},
	{ "writelong",				memory_writedword			},
	{ "gbromreadbyteunsigned",	memory_gbromreadbyte		},
	{ "gbromreadwordunsigned",	memory_gbromreadword		},
	{ "gbromreaddwordunsigned",	memory_gbromreaddword		},
	{ "gbromreadshort",			memory_gbromreadword		},
	{ "gbromreadshortunsigned",	memory_gbromreadword		},
	{ "gbromreadshortsigned",	memory_gbromreadwordsigned	},
	{ "gbromreadlong",			memory_gbromreaddword		},
	{ "gbromreadlongunsigned",	memory_gbromreaddword		},
	{ "gbromreadlongsigned",	memory_gbromreaddwordsigned	},

	// memory hooks
	{ "registerwrite",	   memory_registerwrite			 },
	{ "registerread",	   memory_registerread			 },
	{ "registerexec",	   memory_registerexec			 },
	// alternate names
	{ "register",		   memory_registerwrite			 },
	{ "registerrun",	   memory_registerexec			 },
	{ "registerexecute",   memory_registerexec			 },

	{ NULL,				   NULL							 }
};

static const struct luaL_reg joypadlib[] = {
	{ "get",	  joypad_get	  },
	{ "getdown",  joypad_getdown  },
	{ "getup",	  joypad_getup	  },
	{ "set",	  joypad_set	  },

	// alternative names
	{ "read",	  joypad_get	  },
	{ "write",	  joypad_set	  },
	{ "readdown", joypad_getdown  },
	{ "readup",	  joypad_getup	  },
	{ NULL,		  NULL			  }
};

static const struct luaL_reg savestatelib[] = {
	{ "create", savestate_create },
	{ "save",	savestate_save	 },
	{ "load",	savestate_load	 },

	{ NULL,		NULL			 }
};

static const struct luaL_reg movielib[] = {
	{ "active",			  movie_isactive				},
	{ "recording",		  movie_isrecording				},
	{ "playing",		  movie_isplaying				},
	{ "mode",			  movie_getmode					},

	{ "length",			  movie_getlength				},
	{ "author",			  movie_getauthor				},
	{ "name",			  movie_getfilename				},
	{ "rerecordcount",	  movie_rerecordcount			},
	{ "setrerecordcount", movie_setrerecordcount		},

	{ "rerecordcounting", movie_rerecordcounting		},
	{ "framecount",		  vba_framecount				}, // for those familiar with
															// other emulators that have
															// movie.framecount()
															// instead of
															// emulatorname.framecount()

	{ "stop",			  movie_stop					},

	// alternative names
	{ "close",			  movie_stop					},
	{ "getauthor",		  movie_getauthor				},
	{ "getname",		  movie_getfilename				},
	{ NULL,				  NULL							}
};

static const struct luaL_reg guilib[] = {
	{ "register",	  gui_register		   },
	{ "text",		  gui_text			   },
	{ "box",		  gui_drawbox		   },
	{ "line",		  gui_drawline		   },
	{ "pixel",		  gui_drawpixel		   },
	{ "opacity",	  gui_setopacity	   },
	{ "transparency", gui_transparency	   },
	{ "popup",		  gui_popup			   },
	{ "parsecolor",	  gui_parsecolor	   },
	{ "gdscreenshot", gui_gdscreenshot	   },
	{ "gdoverlay",	  gui_gdoverlay		   },
	{ "getpixel",	  gui_getpixel		   },

	// alternative names
	{ "drawtext",	  gui_text			   },
	{ "drawbox",	  gui_drawbox		   },
	{ "drawline",	  gui_drawline		   },
	{ "drawpixel",	  gui_drawpixel		   },
	{ "setpixel",	  gui_drawpixel		   },
	{ "writepixel",	  gui_drawpixel		   },
	{ "rect",		  gui_drawbox		   },
	{ "drawrect",	  gui_drawbox		   },
	{ "drawimage",	  gui_gdoverlay		   },
	{ "image",		  gui_gdoverlay		   },
	{ "readpixel",	  gui_getpixel		   },
	{ NULL,			  NULL				   }
};

static const struct luaL_reg inputlib[] = {
	{ "get",  input_getcurrentinputstatus  },

	// alternative names
	{ "read", input_getcurrentinputstatus  },
	{ NULL,	  NULL						   }
};

static const struct luaL_reg soundlib[] = {
	{ "get",  sound_get					   },

	// alternative names
	{ NULL,	  NULL						   }
};

// gocha: since vba dumps avi so badly,
// I add avilib as a workaround for enhanced video encoding.
static const struct luaL_reg avilib[] = {
	{ "framecount", avi_framecount },
	{ "pause",		avi_pause	   },
	{ "resume",		avi_resume	   },
	{ NULL,			NULL		   }
};

void CallExitFunction(void)
{
	if (!LUA)
		return;

	lua_settop(LUA, 0);
	lua_getfield(LUA, LUA_REGISTRYINDEX, luaCallIDStrings[LUACALL_BEFOREEXIT]);

	int errorcode = 0;
	if (lua_isfunction(LUA, -1))
	{
		errorcode = lua_pcall(LUA, 0, 0, 0);
	}

	if (errorcode)
		HandleCallbackError(LUA);
}

void VBALuaFrameBoundary(void)
{
	//	printf("Lua Frame\n");

	lua_joypads_used = 0;

	// HA!
	if (!LUA || !luaRunning)
		return;

	// Our function needs calling
	lua_settop(LUA, 0);
	lua_getfield(LUA, LUA_REGISTRYINDEX, frameAdvanceThread);

	lua_State *thread = lua_tothread(LUA, 1);

	// Lua calling C must know that we're busy inside a frame boundary
	frameBoundary		= true;
	frameAdvanceWaiting = false;

	numTries = 1000;

	int result = lua_resume(thread, 0);

	if (result == LUA_YIELD)
	{
		// Okay, we're fine with that.
	}
	else if (result != 0)
	{
		// Done execution by bad causes
		VBALuaOnStop();
		lua_pushnil(LUA);
		lua_setfield(LUA, LUA_REGISTRYINDEX, frameAdvanceThread);
		lua_pushnil(LUA);
		lua_setfield(LUA, LUA_REGISTRYINDEX, guiCallbackTable);

		// Error?
//#if (defined(WIN32) && !defined(SDL))
//			info_print(info_uid, lua_tostring(thread, -1)); //AfxGetApp()->m_pMainWnd->MessageBox(lua_tostring(thread, -1), "Lua run error", MB_OK | MB_ICONSTOP);
//#else
//			fprintf(stderr, "Lua thread bombed out: %s\n", lua_tostring(thread, -1));
//#endif
		printerror(thread, -1);
	}
	else
	{
		VBALuaOnStop();
		printf("Script died of natural causes.\n");
	}

	// Past here, VBA actually runs, so any Lua code is called mid-frame. We must
	// not do anything too stupid, so let ourselves know.
	frameBoundary = false;

	if (!frameAdvanceWaiting)
	{
		VBALuaOnStop();
	}
}

/**
* Loads and runs the given Lua script.
* The emulator MUST be paused for this function to be
* called. Otherwise, all frame boundary assumptions go out the window.
*
* Returns true on success, false on failure.
*/
int VBALoadLuaCode(const char *filename)
{
	if (!DemandLua())
	{
		return 0;
	}

	static bool sfmtInitialized = false;
	if (!sfmtInitialized)
	{
		init_gen_rand((unsigned)time(NULL));
		sfmtInitialized = true;
	}

	if (filename != luaScriptName)
	{
		if (luaScriptName)
			free(luaScriptName);
		luaScriptName = strdup(filename);
	}

	//stop any lua we might already have had running
	VBALuaStop();

	// Set current directory from filename (for dofile)
	char  dir[_MAX_PATH];
	char *slash, *backslash;
	strcpy(dir, filename);
	slash = strrchr(dir, '/');
	backslash = strrchr(dir, '\\');
	if (!slash || (backslash && backslash < slash))
		slash = backslash;
	if (slash)
	{
		slash[1] = '\0'; // keep slash itself for some reasons
		chdir(dir);
	}

	if (!LUA)
	{
		LUA = lua_open();
		luaL_openlibs(LUA);

		luaL_register(LUA, "emu", vbalib); // added for better cross-emulator compatibility
		luaL_register(LUA, "vba", vbalib); // kept for backward compatibility
		luaL_register(LUA, "memory", memorylib);
		luaL_register(LUA, "joypad", joypadlib);
		luaL_register(LUA, "savestate", savestatelib);
		luaL_register(LUA, "movie", movielib);
		luaL_register(LUA, "gui", guilib);
		luaL_register(LUA, "input", inputlib);
		luaL_register(LUA, "sound", soundlib);
		luaL_register(LUA, "bit", bit_funcs); // LuaBitOp library
		luaL_register(LUA, "avi", avilib); // workaround for enhanced video encoding
		lua_settop(LUA, 0); // clean the stack, because each call to luaL_register leaves a table on top

		// register a few utility functions outside of libraries (in the global namespace)
		lua_register(LUA, "print", print);
		lua_register(LUA, "tostring", tostring);
		lua_register(LUA, "addressof", addressof);
		lua_register(LUA, "copytable", copytable);

		// old bit operation functions
		lua_register(LUA, "AND", bit_band);
		lua_register(LUA, "OR", bit_bor);
		lua_register(LUA, "XOR", bit_bxor);
		lua_register(LUA, "SHIFT", bit_bshift_emulua);
		lua_register(LUA, "BIT", bitbit);

		luabitop_validate(LUA);

		lua_pushstring(LUA, "math");
		lua_gettable(LUA, LUA_GLOBALSINDEX);
		lua_pushcfunction(LUA, sfmt_random);
		lua_setfield(LUA, -2, "random");
		lua_pushcfunction(LUA, sfmt_randomseed);
		lua_setfield(LUA, -2, "randomseed");
		lua_settop(LUA, 0);

		// push arrays for storing hook functions in
		for (int i = 0; i < LUAMEMHOOK_COUNT; i++)
		{
			lua_newtable(LUA);
			lua_setfield(LUA, LUA_REGISTRYINDEX, luaMemHookTypeStrings[i]);
		}
	}

	// We make our thread NOW because we want it at the bottom of the stack.
	// If all goes wrong, we let the garbage collector remove it.
	lua_State *thread = lua_newthread(LUA);

	// Load the data
	int result = luaL_loadfile(LUA, filename);

	if (result)
	{
		//#if (defined(WIN32) && !defined(SDL))
		//		info_print(info_uid, lua_tostring(LUA, -1)); //Clear_Sound_Buffer();
		// AfxGetApp()->m_pMainWnd->MessageBox(lua_tostring(LUA, -1), "Lua load error", MB_OK | MB_ICONSTOP);
		//#else
		//		fprintf(stderr, "Failed to compile file: %s\n", lua_tostring(LUA, -1));
		//#endif
		printerror(LUA, -1);

		// Wipe the stack. Our thread
		lua_settop(LUA, 0);
		return 0; // Oh shit.
	}

	// Get our function into it
	lua_xmove(LUA, thread, 1);

	// Save the thread to the registry. This is why I make the thread FIRST.
	lua_setfield(LUA, LUA_REGISTRYINDEX, frameAdvanceThread);

	// Initialize settings
	luaRunning = true;
	skipRerecords = false;
	numMemHooks = 0;
	transparencyModifier = 255; // opaque
	lua_joypads_used = 0; // not used
	for (int i = 0; i < 4; ++i)
	{
		lua_input_display_remap[i].from = 0;
		lua_next_input_display_remap[i].from = 0;
	}
	//wasPaused = systemIsPaused();
	//systemSetPause(false);

	// Set up our protection hook to be executed once every 10,000 bytecode instructions.
	lua_sethook(thread, VBALuaHookFunction, LUA_MASKCOUNT, 10000);

#ifdef WIN32
	info_print = PrintToWindowConsole;
	info_onstart = WinLuaOnStart;
	info_onstop = WinLuaOnStop;
	if (!LuaConsoleHWnd)
		LuaConsoleHWnd = CreateDialog(AfxGetInstanceHandle(), MAKEINTRESOURCE(IDD_LUA),
			AfxGetMainWnd()->GetSafeHwnd(), (DLGPROC)DlgLuaScriptDialog);
	info_uid = (int)LuaConsoleHWnd;
#else
	info_print = NULL;
	info_onstart = NULL;
	info_onstop = NULL;
#endif
	if (info_onstart)
		info_onstart(info_uid);

	// And run it right now. :)
	VBALuaFrameBoundary();
	extern int textMethod;
	if (textMethod == 0)
	{
		int pitch = theApp.filterWidth * (systemColorDepth / 8) + (systemColorDepth == 24 ? 0 : 4);
		systemRenderLua(&pix[pitch], pitch);
	}

	// We're done.
	return 1;
}

/**
* Equivalent to repeating the last VBALoadLuaCode() call.
*/
int VBAReloadLuaCode(void)
{
	if (!luaScriptName)
	{
		systemScreenMessage("There's no script to reload.");
		return 0;
	}
	else
		return VBALoadLuaCode(luaScriptName);
}

/**
* Terminates a running Lua script by killing the whole Lua engine.
*
* Always safe to call, except from within a lua call itself (duh).
*
*/
void VBALuaStop(void)
{
	if (!DemandLua())
		return;

	//already killed
	if (!LUA)
		return;

	//execute the user's shutdown callbacks
	CallExitFunction();

	/*info.*/ numMemHooks = 0;
	for (int i = 0; i < LUAMEMHOOK_COUNT; i++)
		CalculateMemHookRegions((LuaMemHookType)i);

	//sometimes iup uninitializes com
	//MBG TODO - test whether this is really necessary. i dont think it is
#if (defined(WIN32) && !defined(SDL))
	CoInitialize(0);
#endif

	if (info_onstop)
		info_onstop(info_uid);

	//lua_gc(LUA,LUA_GCCOLLECT,0);
	lua_close(LUA); // this invokes our garbage collectors for us
	LUA = NULL;
	VBALuaOnStop();
}

/**
* Returns true if there is a Lua script running.
*
*/
int VBALuaRunning(void)
{
	// FIXME: return false when no callback functions are registered.
	return (int) (LUA != NULL); // should return true if callback functions are active.
}

/**
* Returns true if Lua would like to steal the given joypad control.
*
* Range is 0 through 3
*/
int VBALuaUsingJoypad(int which)
{
	if (which < 0 || which > 3)
		which = systemGetDefaultJoypad();
	return lua_joypads_used & (1 << which);
}

/**
* Reads the buttons Lua is feeding for the given joypad, in the same
* format as the OS-specific code.
*
* <del>This function must not be called more than once per frame. </del>Ideally exactly once
* per frame (if VBALuaUsingJoypad says it's safe to do so)
*/
int VBALuaReadJoypad(int which)
{
	if (which < 0 || which > 3)
		which = systemGetDefaultJoypad();

	//lua_joypads_used &= ~(1 << which);
	return lua_joypads[which];
}

/**
* Returns true if Lua would like to remap input display.
*
* Range is 0 through 3
*/
int VBALuaRemappingInputDisplay(int which)
{
	if (which < 0 || which > 3)
		which = systemGetDefaultJoypad();
	return LUA && (lua_input_display_remap[which].from || lua_next_input_display_remap[which].from);
}

/**
* Return remapped input display.
*
* Range is 0 through 3
* Input/returned values are in the platform-specific raw format
*/
int VBALuaRemapInputDisplay(int which, int input, enum LuaJoypadType padtype)
{
	int output = 0;

	if (which < 0 || which > 3)
		which = systemGetDefaultJoypad();

	LuaInputDisplayRemap *remap = lua_input_display_remap;
	if (padtype == LuaJoypadType::LUAJOYPAD_PLAYBACK)
		remap = lua_next_input_display_remap;

	for (int i = 0; i < 10; ++i)
	{
		if ((input & remap[which].from & (1 << i)) != 0)
			output |= remap[which].to[i];
		else
			output |= input & (1 << i);
	}

	return output;
}

/**
* If this function returns true, the movie code should NOT increment
* the rerecord count for a load-state.
*
* This function will not return true if a script is not running.
*/
bool8 VBALuaRerecordCountSkip(void)
{
	// FIXME: return true if (there are any active callback functions && skipRerecords)
	return LUA && luaRunning && skipRerecords;
}

/**
* Given a screen with the indicated resolution,
* draw the current GUI onto it.
*/
void VBALuaGui(uint8 *screen, int pitch, int width, int height)
{
	if (!LUA /* || !luaRunning*/)
		return;

	// First, check if we're being called by anybody
	lua_getfield(LUA, LUA_REGISTRYINDEX, guiCallbackTable);

	if (lua_isfunction(LUA, -1))
	{
		// We call it now
		numTries = 1000;

		int ret = lua_pcall(LUA, 0, 0, 0);
		if (ret != 0)
		{
			// This is grounds for trashing the function
			// Note: This must be done before the messagebox pops up,
			//		 otherwise the messagebox will cause a paint event which causes a weird
			//		 infinite call sequence that makes Snes9x silently exit with error code 3,
			//		 if a Lua GUI function crashes. (nitsuja)
			lua_pushnil(LUA);
			lua_setfield(LUA, LUA_REGISTRYINDEX, guiCallbackTable);

#if (defined(WIN32) && !defined(SDL))
			info_print(info_uid, lua_tostring(LUA, -1)); //AfxGetApp()->m_pMainWnd->MessageBox(lua_tostring(LUA, -1), "Lua Error
														// in GUI function", MB_OK);
#else
			fprintf(stderr, "Lua error in gui.register function: %s\n", lua_tostring(LUA, -1));
#endif
			printerror(LUA, -1);
		}
	}

	// And wreak the stack
	lua_settop(LUA, 0);

	if (!gui_used)
		return;

	gui_used = false;

	//if (width > LUA_SCREEN_WIDTH)
	//	width = LUA_SCREEN_WIDTH;
	//if (height > LUA_SCREEN_HEIGHT)
	//	height = LUA_SCREEN_HEIGHT;

	GetColorFunc getColor;
	SetColorFunc setColor;
	getColorIOFunc(systemColorDepth, &getColor, &setColor);

	for (int y = 0; y < height; y++)
	{
		uint8 *scr = &screen[y * pitch];
		for (int x = 0; x < width; x++, scr += systemColorDepth / 8)
		{
			const uint8 gui_alpha = gui_data[(y * LUA_SCREEN_WIDTH + x) * 4 + 3];
			if (gui_alpha == 0)
			{
				// do nothing
				continue;
			}

			const uint8 gui_red	  = gui_data[(y * LUA_SCREEN_WIDTH + x) * 4 + 2];
			const uint8 gui_green = gui_data[(y * LUA_SCREEN_WIDTH + x) * 4 + 1];
			const uint8 gui_blue  = gui_data[(y * LUA_SCREEN_WIDTH + x) * 4];
			int			red, green, blue;

			if (gui_alpha == 255)
			{
				// direct copy
				red	  = gui_red;
				green = gui_green;
				blue  = gui_blue;
			}
			else
			{
				// alpha-blending
				uint8 scr_red, scr_green, scr_blue;
				getColor(scr, &scr_red, &scr_green, &scr_blue);
				red	  = (((int)gui_red - scr_red) * gui_alpha / 255 + scr_red) & 255;
				green = (((int)gui_green - scr_green) * gui_alpha / 255 + scr_green) & 255;
				blue  = (((int)gui_blue - scr_blue) * gui_alpha / 255 + scr_blue) & 255;
			}

			setColor(scr, (uint8) red, (uint8) green, (uint8) blue);
		}
	}

	return;
}

void VBALuaClearGui(void)
{
	gui_used = false;
}

lua_State *VBAGetLuaState()
{
	return LUA;
}

char *VBAGetLuaScriptName()
{
	return luaScriptName;
}

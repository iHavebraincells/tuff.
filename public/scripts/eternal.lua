-- ============================================================
--   eternal | clean rewrite
--   fixes: duplicate vars, wrong config keys, esp cleanup,
--          prison life filter, godmode key, scope issues
-- ============================================================

-- UI Library
local ui = loadstring(game:HttpGet("https://cdn.bxsh.info/UIlibrary's/eternal.lua"))()

-- Services
local players    = game:GetService("Players")
local runservice = game:GetService("RunService")
local uis        = game:GetService("UserInputService")

-- Globals
local camera   = workspace.CurrentCamera
local lp       = players.LocalPlayer
local lp_char  = lp.Character or lp.CharacterAdded:Wait()
local esp_objects = {}

-- ============================================================
--   CONFIGURATION
-- ============================================================
local cfg = {
	visuals = {
		masterswitch = false,

		checks = {
			client           = false,
			dead             = false,
			team             = false,
			neutral_as_enemy = false,
			visible          = false,
			distance         = false,
			health           = false,
			max_dist         = 1000,
			min_health       = 20,
		},

		prisonlife = {
			guards   = false,
			inmates  = false,
			criminals = false,
		},

		box = {
			enabled = false,
			outline = false,
			color   = Color3.new(134/255, 86/255, 255/255),
		},

		name = {
			enabled = false,
			outline = false,
			color   = Color3.new(156/255, 117/255, 255/255),
		},

		distance = {
			enabled = false,
			outline = false,
			color   = Color3.new(156/255, 117/255, 255/255),
		},

		skeleton = {
			enabled = false,
			outline = false,
			color   = Color3.new(134/255, 86/255, 255/255),
			dots = {
				enabled = false,
				outline = false,
				color   = Color3.new(134/255, 86/255, 255/255),
			},
		},
	},

	player = {
		walkspeed = { enabled = false, value = 16 },
		jumppower = { enabled = false, value = 50 },
		inf_jump  = false,
		fly       = { enabled = false, speed = 50 },
		noclip    = false,
		godmode   = false,  -- FIXED: was split between player/combat
	},

	combat = {
		fov = {
			enabled = false,
			radius  = 100,
			color   = Color3.new(1, 1, 1),
		},
		aimlock = {
			enabled       = false,
			target_part   = "Head",
			smoothness    = 0.25,
			use_fov       = true,
			right_click_only = true,
		},
	},

	weaponmods = {
		rainbow_gun = false,
	},
}

-- ============================================================
--   SKELETON DATA
-- ============================================================
local bone_connections_r6 = {
	{"Head","Torso"},
	{"Torso","Right Arm"},
	{"Torso","Left Arm"},
	{"Torso","Right Leg"},
	{"Torso","Left Leg"},
}

local bone_connections_r15 = {
	{"Head","UpperTorso"},
	{"UpperTorso","LowerTorso"},
	{"LowerTorso","LeftUpperLeg"},
	{"LowerTorso","RightUpperLeg"},
	{"LeftUpperLeg","LeftLowerLeg"},
	{"LeftLowerLeg","LeftFoot"},
	{"RightUpperLeg","RightLowerLeg"},
	{"RightLowerLeg","RightFoot"},
	{"UpperTorso","LeftUpperArm"},
	{"UpperTorso","RightUpperArm"},
	{"LeftUpperArm","LeftLowerArm"},
	{"LeftLowerArm","LeftHand"},
	{"RightUpperArm","RightLowerArm"},
	{"RightLowerArm","RightHand"},
}

local all_bones_r6 = {
	"Head","Torso","Right Arm","Left Arm","Right Leg","Left Leg",
}

local all_bones_r15 = {
	"Head","UpperTorso","LowerTorso",
	"RightUpperLeg","LeftUpperLeg","RightLowerLeg","LeftLowerLeg",
	"RightFoot","LeftFoot","RightUpperArm","LeftUpperArm",
	"RightLowerArm","LeftLowerArm","RightHand","LeftHand",
}

-- ============================================================
--   HELPERS
-- ============================================================
local function draw(kind, opts)
	local obj = Drawing.new(kind)
	for k, v in pairs(opts) do obj[k] = v end
	return obj
end

local function w2s(world)
	return camera:WorldToViewportPoint(world)
end

local function color3_to_hsvar(col)
	local h, s, v = col:ToHSV()
	return { h, s, v, 0, false }
end

local function get_hum()
	local c = lp.Character
	return c and c:FindFirstChildOfClass("Humanoid")
end

local function get_hrp()
	local c = lp.Character
	return c and c:FindFirstChild("HumanoidRootPart")
end

local function is_visible(player)
	local char = player.Character
	if not char then return false end

	local origin = camera.CFrame.Position
	local rp = RaycastParams.new()
	rp.FilterType = Enum.RaycastFilterType.Exclude
	rp.FilterDescendantsInstances = { char, lp_char }

	for _, child in pairs(char:GetChildren()) do
		if not child:IsA("BasePart") then continue end
		local dir = child.Position - origin
		local res = workspace:Raycast(origin, dir, rp)
		if res == nil then return true end
	end
	return false
end

local function get_player_bounds(player)
	local char = player and player.Character
	if not char then return false end

	local verts = {
		Vector3.new(1,1,1), Vector3.new(1,1,-1),
		Vector3.new(1,-1,1), Vector3.new(1,-1,-1),
		Vector3.new(-1,1,1), Vector3.new(-1,1,-1),
		Vector3.new(-1,-1,1), Vector3.new(-1,-1,-1),
	}

	local min_x, min_y =  math.huge,  math.huge
	local max_x, max_y = -math.huge, -math.huge
	local valid = false

	for _, child in ipairs(char:GetChildren()) do
		if not child:IsA("BasePart") then continue end
		local cf = child.CFrame
		local sz = child.Size
		for _, v in ipairs(verts) do
			local world = cf * Vector3.new(v.X*sz.X/2, v.Y*sz.Y/2, v.Z*sz.Z/2)
			local screen = w2s(world)
			min_x = math.min(min_x, screen.X)
			min_y = math.min(min_y, screen.Y)
			max_x = math.max(max_x, screen.X)
			max_y = math.max(max_y, screen.Y)
			valid = true
		end
	end

	return valid, Vector2.new(min_x, min_y), Vector2.new(max_x, max_y)
end

-- ============================================================
--   WINDOW / WATERMARK
-- ============================================================
local username = lp and lp.Name or "Unknown"
local window   = ui:Window({ Name = "eternal | @" .. username })

do
	local last = tick()
	local watermark = window:Watermark({
		Title   = "eternal | discord.gg/bxsh | " .. os.date("%d-%m-%y"),
		Enabled = true,
		Fixed   = true,
	})

	runservice.Heartbeat:Connect(function()
		local now = tick()
		if now - last >= 1 then
			watermark.Title = "eternal | @" .. username .. " | " .. os.date("%d-%m-%y")
			last = now
		end
	end)
end

-- ============================================================
--   PLAYER TAB
-- ============================================================
local pt       = window:Tab({ Name = "player" })
local movement = pt:Section({ Name = "movement", Side = "Left" })
local health_s = pt:Section({ Name = "health",   Side = "Right" })

-- WalkSpeed
movement:Toggle({
	Name = "Custom WalkSpeed", Value = false,
	Callback = function(val)
		cfg.player.walkspeed.enabled = val
		local h = get_hum()
		if h then h.WalkSpeed = val and cfg.player.walkspeed.value or 16 end
	end,
})
movement:Slider({
	Name = "WalkSpeed Value", Min = 0, Max = 500, Value = 16, Precise = 1,
	Callback = function(val)
		cfg.player.walkspeed.value = val
		if cfg.player.walkspeed.enabled then
			local h = get_hum()
			if h then h.WalkSpeed = val end
		end
	end,
})

-- JumpPower
movement:Toggle({
	Name = "Custom JumpPower", Value = false,
	Callback = function(val)
		cfg.player.jumppower.enabled = val
		local h = get_hum()
		if h then h.JumpPower = val and cfg.player.jumppower.value or 50 end
	end,
})
movement:Slider({
	Name = "JumpPower Value", Min = 0, Max = 500, Value = 50, Precise = 1,
	Callback = function(val)
		cfg.player.jumppower.value = val
		if cfg.player.jumppower.enabled then
			local h = get_hum()
			if h then h.JumpPower = val end
		end
	end,
})

-- Inf Jump
local inf_jump_conn = nil
movement:Toggle({
	Name = "Inf Jump", Value = false,
	Callback = function(val)
		cfg.player.inf_jump = val
		if val then
			inf_jump_conn = uis.JumpRequest:Connect(function()
				local h = get_hum()
				if h then h:ChangeState(Enum.HumanoidStateType.Jumping) end
			end)
		else
			if inf_jump_conn then inf_jump_conn:Disconnect() inf_jump_conn = nil end
		end
	end,
})

-- Fly
local fly_conn, fly_bv, fly_bg = nil, nil, nil

local function stop_fly()
	cfg.player.fly.enabled = false
	if fly_conn then fly_conn:Disconnect() fly_conn = nil end
	if fly_bv   then fly_bv:Destroy()      fly_bv   = nil end
	if fly_bg   then fly_bg:Destroy()      fly_bg   = nil end
	local h = get_hum()
	if h then h.PlatformStand = false end
end

movement:Toggle({
	Name = "Fly", Value = false,
	Callback = function(val)
		cfg.player.fly.enabled = val
		if not val then stop_fly() return end

		local hrp = get_hrp()
		local hum = get_hum()
		if not hrp or not hum then cfg.player.fly.enabled = false return end

		hum.PlatformStand = true

		fly_bv = Instance.new("BodyVelocity")
		fly_bv.Velocity  = Vector3.zero
		fly_bv.MaxForce  = Vector3.new(1e9, 1e9, 1e9)
		fly_bv.Parent    = hrp

		fly_bg = Instance.new("BodyGyro")
		fly_bg.MaxTorque = Vector3.new(1e9, 1e9, 1e9)
		fly_bg.D         = 100
		fly_bg.CFrame    = hrp.CFrame
		fly_bg.Parent    = hrp

		fly_conn = runservice.RenderStepped:Connect(function()
			if not cfg.player.fly.enabled then stop_fly() return end
			local r = get_hrp()
			if not r then stop_fly() return end

			local speed = cfg.player.fly.speed
			local cam   = workspace.CurrentCamera
			local dir   = Vector3.zero

			if uis:IsKeyDown(Enum.KeyCode.W)            then dir += cam.CFrame.LookVector           end
			if uis:IsKeyDown(Enum.KeyCode.S)            then dir -= cam.CFrame.LookVector           end
			if uis:IsKeyDown(Enum.KeyCode.A)            then dir -= cam.CFrame.RightVector          end
			if uis:IsKeyDown(Enum.KeyCode.D)            then dir += cam.CFrame.RightVector          end
			if uis:IsKeyDown(Enum.KeyCode.Space)        then dir += Vector3.new(0, 1, 0)            end
			if uis:IsKeyDown(Enum.KeyCode.LeftControl)  then dir -= Vector3.new(0, 1, 0)            end

			fly_bv.Velocity = dir.Magnitude > 0 and (dir.Unit * speed) or Vector3.zero
			fly_bg.CFrame   = cam.CFrame
		end)
	end,
})
movement:Slider({
	Name = "Fly Speed", Min = 10, Max = 300, Value = 50, Precise = 1,
	Callback = function(val) cfg.player.fly.speed = val end,
})

-- Noclip
local noclip_conn = nil
movement:Toggle({
	Name = "Noclip", Value = false,
	Callback = function(val)
		cfg.player.noclip = val
		if val then
			noclip_conn = runservice.Stepped:Connect(function()
				if not cfg.player.noclip then return end
				local c = lp.Character
				if not c then return end
				for _, p in pairs(c:GetDescendants()) do
					if p:IsA("BasePart") then p.CanCollide = false end
				end
			end)
		else
			if noclip_conn then noclip_conn:Disconnect() noclip_conn = nil end
			local c = lp.Character
			if c then
				local r = c:FindFirstChild("HumanoidRootPart")
				if r then r.CanCollide = true end
			end
		end
	end,
})

-- Godmode  (FIXED: key is cfg.player.godmode, not cfg.combat.godmode)
local godmode_conn = nil
health_s:Toggle({
	Name = "Godmode", Value = false,
	Callback = function(val)
		cfg.player.godmode = val
		local h = get_hum()
		if not h then return end
		if val then
			h.MaxHealth = math.huge
			h.Health    = math.huge
			godmode_conn = h.HealthChanged:Connect(function()
				if cfg.player.godmode then h.Health = math.huge end
			end)
		else
			if godmode_conn then godmode_conn:Disconnect() godmode_conn = nil end
			h.MaxHealth = 100
			h.Health    = 100
		end
	end,
})

-- Reapply on respawn
lp.CharacterAdded:Connect(function(char)
	lp_char = char
	local hum = char:WaitForChild("Humanoid", 5)
	if not hum then return end

	if cfg.player.walkspeed.enabled then hum.WalkSpeed = cfg.player.walkspeed.value end
	if cfg.player.jumppower.enabled  then hum.JumpPower  = cfg.player.jumppower.value  end

	if cfg.player.godmode then
		hum.MaxHealth = math.huge
		hum.Health    = math.huge
		hum.HealthChanged:Connect(function()
			if cfg.player.godmode then hum.Health = math.huge end
		end)
	end
end)

-- ============================================================
--   COMBAT TAB
-- ============================================================
local ct        = window:Tab({ Name = "combat" })
local aim_s     = ct:Section({ Name = "aim", Side = "Left" })

-- FOV circle
local fov_circle = draw("Circle", {
	Visible = false, Color = Color3.new(1,1,1),
	Thickness = 1, Radius = 100, Filled = false, ZIndex = 5,
})

runservice.RenderStepped:Connect(function()
	if not cfg.combat.fov.enabled then
		fov_circle.Visible = false
		return
	end
	local mouse       = uis:GetMouseLocation()
	fov_circle.Position = Vector2.new(mouse.X, mouse.Y)
	fov_circle.Radius   = cfg.combat.fov.radius
	fov_circle.Color    = cfg.combat.fov.color
	fov_circle.Visible  = true
end)

-- Aimlock
local aim_target = nil

local function get_closest_target()
	local closest  = nil
	local shortest = math.huge
	local mousePos = uis:GetMouseLocation()

	for _, p in ipairs(players:GetPlayers()) do
		if p == lp or not p.Character then continue end
		local char = p.Character
		local hum  = char:FindFirstChild("Humanoid")
		local root = char:FindFirstChild("HumanoidRootPart")
		local head = char:FindFirstChild("Head")

		if not hum or hum.Health <= 0 then continue end

		local targetPart = (cfg.combat.aimlock.target_part == "Head" and head) or root
		if not targetPart then continue end

		local screenPos, onScreen = camera:WorldToViewportPoint(targetPart.Position)
		if not onScreen then continue end

		local dist = (Vector2.new(screenPos.X, screenPos.Y) - mousePos).Magnitude

		if cfg.combat.aimlock.use_fov and dist > cfg.combat.fov.radius then continue end

		if dist < shortest then
			shortest = dist
			closest  = targetPart
		end
	end
	return closest
end

runservice.RenderStepped:Connect(function()
	if not cfg.combat.aimlock.enabled then
		aim_target = nil
		return
	end
	if not uis:IsMouseButtonPressed(Enum.UserInputType.MouseButton2) then
		aim_target = nil
		return
	end

	aim_target = get_closest_target()

	if aim_target then
		local targetPos  = camera:WorldToViewportPoint(aim_target.Position)
		local currentPos = uis:GetMouseLocation()
		local direction  = Vector2.new(targetPos.X, targetPos.Y) - currentPos
		local smoothed   = currentPos + (direction * cfg.combat.aimlock.smoothness)
		local dx = (smoothed.X - currentPos.X) * 0.8
		local dy = (smoothed.Y - currentPos.Y) * 0.8
		pcall(mousemoverel, dx, dy)  -- FIXED: wrapped in pcall; mousemoverel may not exist
	end
end)

-- UI: Aimlock
aim_s:Toggle({
	Name = "Aimlock (Hold Right Click)", Value = false,
	Callback = function(val) cfg.combat.aimlock.enabled = val end,
})
aim_s:Slider({
	Name = "Smoothness", Min = 0.05, Max = 1, Value = 0.25, Precise = 2,
	Callback = function(val) cfg.combat.aimlock.smoothness = val end,
})
aim_s:Toggle({
	Name = "Use FOV", Value = true,
	Callback = function(val) cfg.combat.aimlock.use_fov = val end,
})

local fov_toggle = aim_s:Toggle({
	Name = "FOV Circle", Value = false,
	Callback = function(val)
		cfg.combat.fov.enabled = val
		if not val then fov_circle.Visible = false end
	end,
})
fov_toggle:Colorpicker({
	Value = color3_to_hsvar(Color3.new(1,1,1)),
	Callback = function(_, col3) cfg.combat.fov.color = col3 end,
})
aim_s:Slider({
	Name = "FOV Radius", Min = 10, Max = 500, Value = 100, Precise = 1,
	Callback = function(val) cfg.combat.fov.radius = val end,
})

-- ============================================================
--   WEAPON MODS TAB
-- ============================================================
local wt      = window:Tab({ Name = "weapon mods" })
local gun_s   = wt:Section({ Name = "gun mods | MAY NOT WORK DEPENDING ON GAME", Side = "Left" })

local rainbow_conn   = nil
local rainbow_hue    = 0
local original_colors = {}

local function get_equipped_tool()
	local c = lp.Character
	return c and c:FindFirstChildOfClass("Tool")
end

local function get_tool_parts(tool)
	local parts = {}
	if not tool then return parts end
	for _, v in ipairs(tool:GetDescendants()) do
		if v:IsA("BasePart") then table.insert(parts, v) end
	end
	return parts
end

local function save_original_colors(tool)
	original_colors = {}
	for _, part in ipairs(get_tool_parts(tool)) do
		original_colors[part] = { Color = part.Color, Material = part.Material }
	end
end

local function restore_original_colors()
	for part, data in pairs(original_colors) do
		if part and part.Parent then
			part.Color    = data.Color
			part.Material = data.Material
		end
	end
	original_colors = {}
end

local function apply_rainbow(tool, color)
	for _, part in ipairs(get_tool_parts(tool)) do
		if part and part.Parent then
			part.Color    = color
			part.Material = Enum.Material.Neon
		end
	end
end

local function start_rainbow()
	if rainbow_conn then rainbow_conn:Disconnect() end
	local last_tool = nil

	rainbow_conn = runservice.RenderStepped:Connect(function()
		if not cfg.weaponmods.rainbow_gun then return end
		local tool = get_equipped_tool()

		if tool ~= last_tool then
			restore_original_colors()
			if tool then
				task.wait()
				save_original_colors(tool)
			end
			last_tool = tool
		end

		if not tool then return end
		rainbow_hue = (rainbow_hue + 0.01) % 1
		apply_rainbow(tool, Color3.fromHSV(rainbow_hue, 1, 1))
	end)
end

local function stop_rainbow()
	if rainbow_conn then rainbow_conn:Disconnect() rainbow_conn = nil end
	restore_original_colors()
end

gun_s:Toggle({
	Name = "Rainbow Gun", Value = false,
	Callback = function(val)
		cfg.weaponmods.rainbow_gun = val
		if val then start_rainbow() else stop_rainbow() end
	end,
})

lp.CharacterAdded:Connect(function()
	if cfg.weaponmods.rainbow_gun then
		rainbow_hue = 0
		task.wait(1)
		start_rainbow()
	end
end)

-- ============================================================
--   GAME STUFF TAB
-- ============================================================
local gt         = window:Tab({ Name = "game stuff" })
local prison_s   = gt:Section({ Name = "prison life",   Side = "Left"  })
local fleefac_s  = gt:Section({ Name = "flee the fac",  Side = "Right" })

prison_s:Button({
	Name = "Crim Base",
	Callback = function()
		local c   = lp.Character or lp.CharacterAdded:Wait()
		local mdl = workspace:FindFirstChild("Criminals Spawn")
		if mdl and mdl:IsA("Model") then
			c:WaitForChild("HumanoidRootPart").CFrame = mdl:GetPivot() + Vector3.new(0, 5, 0)
		else
			warn("[eternal] Criminals Spawn not found")
		end
	end,
})

prison_s:Button({
	Name = "Prison",
	Callback = function()
		local c   = lp.Character or lp.CharacterAdded:Wait()
		local mdl = workspace:FindFirstChild("Prison_Cellblock")
		if mdl and mdl:IsA("Model") then
			c:WaitForChild("HumanoidRootPart").CFrame = mdl:GetPivot() + Vector3.new(0, 5, 0)
		else
			warn("[eternal] Prison_Cellblock not found")
		end
	end,
})

fleefac_s:Button({
	Name = "Lobby",
	Callback = function()
		local c    = lp.Character or lp.CharacterAdded:Wait()
		local pad  = workspace:FindFirstChild("LobbySpawnPad")
		if pad and pad:IsA("Part") then
			c:WaitForChild("HumanoidRootPart").CFrame = pad:GetPivot() + Vector3.new(0, 5, 0)
		else
			warn("[eternal] LobbySpawnPad not found")
		end
	end,
})

-- ============================================================
--   VISUALS TAB
-- ============================================================
local vt      = window:Tab({ Name = "visuals" })
local basics  = vt:Section({ Name = "basics" })

basics:Toggle({
	Name = "Masterswitch", Value = false,
	Callback = function(val) cfg.visuals.masterswitch = val end,
})

-- Box
local bt = basics:Toggle({
	Name = "Box", Value = false,
	Callback = function(val) cfg.visuals.box.enabled = val end,
})
bt:Colorpicker({
	Value = color3_to_hsvar(cfg.visuals.box.color),
	Callback = function(_, col3) cfg.visuals.box.color = col3 end,
})
basics:Toggle({
	Name = "Box Outline", Value = false,
	Callback = function(val) cfg.visuals.box.outline = val end,
})

-- Name
local nt = basics:Toggle({
	Name = "Name", Value = false,
	Callback = function(val) cfg.visuals.name.enabled = val end,
})
nt:Colorpicker({
	Value = color3_to_hsvar(cfg.visuals.name.color),
	Callback = function(_, col3) cfg.visuals.name.color = col3 end,
})
basics:Toggle({
	Name = "Name Outline", Value = false,
	Callback = function(val) cfg.visuals.name.outline = val end,
})

-- Distance
local dst = basics:Toggle({
	Name = "Distance", Value = false,
	Callback = function(val) cfg.visuals.distance.enabled = val end,
})
dst:Colorpicker({
	Value = color3_to_hsvar(cfg.visuals.distance.color),
	Callback = function(_, col3) cfg.visuals.distance.color = col3 end,
})
basics:Toggle({
	Name = "Distance Outline", Value = false,
	Callback = function(val) cfg.visuals.distance.outline = val end,
})

-- Skeleton
local skt = basics:Toggle({
	Name = "Skeleton", Value = false,
	Callback = function(val) cfg.visuals.skeleton.enabled = val end,
})
skt:Colorpicker({
	Value = color3_to_hsvar(cfg.visuals.skeleton.color),
	Callback = function(_, col3) cfg.visuals.skeleton.color = col3 end,
})
basics:Toggle({
	Name = "Skeleton Outline", Value = false,
	Callback = function(val) cfg.visuals.skeleton.outline = val end,
})

-- Skeleton Dots
local sdt = basics:Toggle({
	Name = "Skeleton Dots", Value = false,
	Callback = function(val) cfg.visuals.skeleton.dots.enabled = val end,
})
sdt:Colorpicker({
	Value = color3_to_hsvar(cfg.visuals.skeleton.dots.color),
	Callback = function(_, col3) cfg.visuals.skeleton.dots.color = col3 end,
})
basics:Toggle({
	Name = "Skeleton Dots Outline", Value = false,
	Callback = function(val) cfg.visuals.skeleton.dots.outline = val end,
})

-- Prison Life ESP filters
basics:Toggle({
	Name = "Guards ESP", Value = false,
	Callback = function(val) cfg.visuals.prisonlife.guards = val end,
})
basics:Toggle({
	Name = "Inmates ESP", Value = false,
	Callback = function(val) cfg.visuals.prisonlife.inmates = val end,
})
basics:Toggle({
	Name = "Criminals ESP", Value = false,
	Callback = function(val) cfg.visuals.prisonlife.criminals = val end,
})

-- ============================================================
--   SETTINGS TAB
-- ============================================================
local sett   = window:Tab({ Name = "settings" })
local checks = sett:Section({ Name = "checks", Side = "Left" })

checks:Toggle({ Name = "Client Check",   Value = false, Callback = function(val) cfg.visuals.checks.client           = val end })
checks:Toggle({ Name = "Dead Check",     Value = false, Callback = function(val) cfg.visuals.checks.dead             = val end })
checks:Toggle({ Name = "Team Check",     Value = false, Callback = function(val) cfg.visuals.checks.team             = val end })

local naet = checks:Toggle({ Name = "Neutral As Enemy", Value = false, Callback = function(val) cfg.visuals.checks.neutral_as_enemy = val end })
naet:Tooltip("If both you and another player are on a neutral team, they will be treated as an enemy.")

checks:Toggle({ Name = "Visible Check",  Value = false, Callback = function(val) cfg.visuals.checks.visible  = val end })
checks:Toggle({ Name = "Distance Check", Value = false, Callback = function(val) cfg.visuals.checks.distance = val end })
checks:Toggle({ Name = "Health Check",   Value = false, Callback = function(val) cfg.visuals.checks.health   = val end })

local ds = checks:Slider({ Name = "Max Distance", Min = 0, Max = 5000, Value = 1000, Precise = 1, Callback = function(val) cfg.visuals.checks.max_dist  = val end })
ds:Tooltip("Players beyond this distance are not shown.")

local hs = checks:Slider({ Name = "Min Health", Min = 0, Max = 100, Value = 20, Precise = 1, Callback = function(val) cfg.visuals.checks.min_health = val end })
hs:Tooltip("Players with less than this health are not shown.")

sett:AddConfigSection("eternal", "Right")

-- ============================================================
--   ESP LOGIC
-- ============================================================
local function add_player_esp(player)
	if esp_objects[player] then return end

	local box = draw("Square", {
		Visible = false, Color = Color3.new(1,1,1),
		Size = Vector2.zero, Thickness = 1, ZIndex = 4,
	})
	local box_outline = draw("Square", {
		Visible = false, Color = Color3.new(0,0,0),
		Size = Vector2.zero, Thickness = 3, ZIndex = 3,
	})
	local name_tag = draw("Text", {
		Visible = false, Color = Color3.new(1,1,1),
		Text = player.Name, Center = true,
		Outline = true, OutlineColor = Color3.new(0,0,0), ZIndex = 4,
	})
	local dist_tag = draw("Text", {
		Visible = false, Color = Color3.new(1,1,1),
		Text = "[ 0.0m ]", Center = true,
		Outline = true, OutlineColor = Color3.new(0,0,0), ZIndex = 4,
	})

	local skeleton = {
		lines          = {},
		joints         = {},
		bone_connections = nil,
		bone_set       = nil,
		rig_detected   = false,
	}

	local objects = {
		box         = box,
		box_outline = box_outline,
		name_tag    = name_tag,
		dist_tag    = dist_tag,
		skeleton    = skeleton,
	}

	local function hide_all()
		box.Visible         = false
		box_outline.Visible = false
		name_tag.Visible    = false
		dist_tag.Visible    = false
		for _, bt in ipairs(skeleton.lines) do
			bt.joint.Visible         = false
			bt.joint_outline.Visible = false
		end
		for _, jt in ipairs(skeleton.joints) do
			jt.dot.Visible     = false
			jt.outline.Visible = false
		end
	end

	local conn = runservice.RenderStepped:Connect(function()
		if not cfg.visuals.masterswitch then hide_all() return end

		-- Client check
		if cfg.visuals.checks.client and player == lp then hide_all() return end

		-- Prison Life filter  (FIXED: check individual bools, not the table)
		local pl = cfg.visuals.prisonlife
		local any_pl_active = pl.guards or pl.inmates or pl.criminals
		if any_pl_active then
			local team = player.Team and player.Team.Name or ""
			local allowed = (team == "Guards" and pl.guards)
				or (team == "Inmates"   and pl.inmates)
				or (team == "Criminals" and pl.criminals)
			if not allowed then hide_all() return end
		end

		-- Team check
		if cfg.visuals.checks.team and player ~= lp then
			local lp_team = lp.Team
			local p_team  = player.Team
			local same_team    = p_team ~= nil and p_team == lp_team
			local both_neutral = lp_team == nil and p_team == nil
			if same_team then hide_all() return end
			if both_neutral and not cfg.visuals.checks.neutral_as_enemy then hide_all() return end
		end

		local char     = player.Character
		if not char then hide_all() return end

		local humanoid = char:FindFirstChildOfClass("Humanoid")

		-- Dead check
		if cfg.visuals.checks.dead then
			if not humanoid or humanoid.Health <= 0
				or humanoid:GetState() == Enum.HumanoidStateType.Dead
			then hide_all() return end
		end

		-- Health check
		if cfg.visuals.checks.health and humanoid and humanoid.Health < cfg.visuals.checks.min_health then
			hide_all() return
		end

		local hrp  = char:FindFirstChild("HumanoidRootPart")
		local head = char:FindFirstChild("Head")
		if not hrp or not head then hide_all() return end

		-- Distance check
		local our_pos = (lp_char and lp_char:FindFirstChild("HumanoidRootPart"))
			and lp_char.HumanoidRootPart.Position
			or  camera.CFrame.Position

		local dist = (our_pos - hrp.Position).Magnitude

		if cfg.visuals.checks.distance and dist > cfg.visuals.checks.max_dist then
			hide_all() return
		end

		-- Visible check
		if cfg.visuals.checks.visible and not is_visible(player) then
			hide_all() return
		end

		-- Build skeleton drawing objects once rig is detected
		if not skeleton.rig_detected then
			if humanoid.RigType == Enum.HumanoidRigType.R6 then
				skeleton.bone_connections = bone_connections_r6
				skeleton.bone_set         = all_bones_r6
			else
				skeleton.bone_connections = bone_connections_r15
				skeleton.bone_set         = all_bones_r15
			end
			skeleton.rig_detected = true

			for idx, pair in ipairs(skeleton.bone_connections) do
				skeleton.lines[idx] = {
					joint         = draw("Line", { Visible=false, Color=Color3.new(1,1,1), Thickness=1, ZIndex=2 }),
					joint_outline = draw("Line", { Visible=false, Color=Color3.new(0,0,0), Thickness=3, ZIndex=1 }),
					from_bone     = pair[1],
					to_bone       = pair[2],
				}
			end

			for _, bone_name in ipairs(skeleton.bone_set) do
				table.insert(skeleton.joints, {
					dot     = draw("Circle", { Visible=false, Color=Color3.new(1,1,1), Thickness=1, Radius=2, Filled=true,  ZIndex=4 }),
					outline = draw("Circle", { Visible=false, Color=Color3.new(0,0,0), Radius=3,    Filled=true,  ZIndex=3 }),
					bone    = bone_name,
				})
			end
		end

		local _, on_screen = w2s(hrp.Position)
		if not on_screen then hide_all() return end

		local head_pos              = w2s(head.Position + Vector3.new(0, 0.5, 0))
		local valid, top_left, bot_right = get_player_bounds(player)
		if not valid then hide_all() return end

		local w = bot_right.X - top_left.X
		local h = bot_right.Y - top_left.Y

		-- Box
		box.Size     = Vector2.new(w, h)
		box.Position = top_left
		box.Color    = cfg.visuals.box.color
		box.Visible  = cfg.visuals.box.enabled

		box_outline.Size     = Vector2.new(w, h)
		box_outline.Position = top_left
		box_outline.Visible  = cfg.visuals.box.outline

		-- Name
		name_tag.Position = Vector2.new(head_pos.X, top_left.Y - 20)
		name_tag.Outline  = cfg.visuals.name.outline
		name_tag.Color    = cfg.visuals.name.color
		name_tag.Visible  = cfg.visuals.name.enabled

		-- Distance
		dist_tag.Text     = string.format("[ %.1fm ]", dist)
		dist_tag.Position = Vector2.new(head_pos.X, top_left.Y + h + 10)
		dist_tag.Outline  = cfg.visuals.distance.outline
		dist_tag.Color    = cfg.visuals.distance.color
		dist_tag.Visible  = cfg.visuals.distance.enabled

		-- Skeleton lines
		for _, bt in ipairs(skeleton.lines) do
			local from = char:FindFirstChild(bt.from_bone)
			local to   = char:FindFirstChild(bt.to_bone)
			if not from or not to then
				bt.joint.Visible         = false
				bt.joint_outline.Visible = false
				continue
			end

			local fp, fv = w2s(from.Position)
			local tp, tv = w2s(to.Position)

			if not fv or not tv then
				bt.joint.Visible         = false
				bt.joint_outline.Visible = false
				continue
			end

			bt.joint.From         = Vector2.new(fp.X, fp.Y)
			bt.joint.To           = Vector2.new(tp.X, tp.Y)
			bt.joint.Color        = cfg.visuals.skeleton.color
			bt.joint.Visible      = cfg.visuals.skeleton.enabled

			bt.joint_outline.From    = Vector2.new(fp.X, fp.Y)
			bt.joint_outline.To      = Vector2.new(tp.X, tp.Y)
			bt.joint_outline.Visible = cfg.visuals.skeleton.outline
		end

		-- Skeleton dots
		for _, jt in ipairs(skeleton.joints) do
			local bone = char:FindFirstChild(jt.bone)
			if not bone then
				jt.dot.Visible     = false
				jt.outline.Visible = false
				continue
			end

			local bp, bv = w2s(bone.Position)
			if not bv then
				jt.dot.Visible     = false
				jt.outline.Visible = false
				continue
			end

			jt.dot.Position     = Vector2.new(bp.X, bp.Y)
			jt.dot.Color        = cfg.visuals.skeleton.dots.color
			jt.dot.Visible      = cfg.visuals.skeleton.dots.enabled

			jt.outline.Position = Vector2.new(bp.X, bp.Y)
			jt.outline.Visible  = cfg.visuals.skeleton.dots.outline
		end
	end)

	esp_objects[player] = { objects = objects, connection = conn }
end

local function remove_player_esp(player)
	local entry = esp_objects[player]
	if not entry then return end

	-- Disconnect the render loop
	if entry.connection and entry.connection.Connected then
		entry.connection:Disconnect()
	end

	local obj = entry.objects

	-- FIXED: destroy drawing objects by key, skip the skeleton table explicitly
	for key, draw_obj in pairs(obj) do
		if key == "skeleton" then continue end
		pcall(function() draw_obj:Destroy() end)
	end

	-- Destroy skeleton lines and dots separately
	for _, bt in ipairs(obj.skeleton.lines) do
		pcall(function() bt.joint:Destroy()         end)
		pcall(function() bt.joint_outline:Destroy() end)
	end
	for _, jt in ipairs(obj.skeleton.joints) do
		pcall(function() jt.dot:Destroy()     end)
		pcall(function() jt.outline:Destroy() end)
	end

	esp_objects[player] = nil
end

-- Init ESP for existing players
for _, p in pairs(players:GetPlayers()) do
	add_player_esp(p)
end

players.PlayerAdded:Connect(function(p)
	p.CharacterAdded:Connect(function()
		task.wait()  -- let character load
		add_player_esp(p)
	end)
end)

players.PlayerRemoving:Connect(function(p)
	remove_player_esp(p)
end)

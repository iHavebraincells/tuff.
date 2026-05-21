--// Aztup UI Library (v3 - Executor Safe)
--// Fixes: LocalPlayer nil on load, AutomaticCanvasSize compat,
--//        Toggle name collision, hover routing, slider ZIndex.

local Players      = game:GetService("Players")
local UIS          = game:GetService("UserInputService")
local TweenService = game:GetService("TweenService")

----------------------------------------------------------------------
-- Library table
----------------------------------------------------------------------
local library = {
    windows     = {},
    gui         = nil,
    _notifQueue = {},
}

----------------------------------------------------------------------
-- HELPERS
----------------------------------------------------------------------

local function create(class, props)
    local obj = Instance.new(class)
    for k, v in pairs(props) do
        if k ~= "Parent" then obj[k] = v end
    end
    if props.Parent then obj.Parent = props.Parent end
    return obj
end

local function addCorner(parent, radius)
    return create("UICorner", { Parent = parent, CornerRadius = UDim.new(0, radius or 6) })
end

local function addPadding(parent, h, v)
    return create("UIPadding", {
        Parent        = parent,
        PaddingLeft   = UDim.new(0, h or 6),
        PaddingRight  = UDim.new(0, h or 6),
        PaddingTop    = UDim.new(0, v or 4),
        PaddingBottom = UDim.new(0, v or 4),
    })
end

local function tween(obj, t, props, style, dir)
    TweenService:Create(obj,
        TweenInfo.new(t, style or Enum.EasingStyle.Quad, dir or Enum.EasingDirection.Out),
        props
    ):Play()
end

-- FIX: LocalPlayer fetched lazily so the library doesn't crash on load
-- in executor environments where LocalPlayer isn't ready yet.
local function getLocalPlayer()
    local lp = Players.LocalPlayer
    if not lp then
        lp = Players:GetPropertyChangedSignal("LocalPlayer"):Wait()
        lp = Players.LocalPlayer
    end
    return lp
end

local function ensureGui(lib)
    if lib.gui and lib.gui.Parent then return lib.gui end

    local lp  = getLocalPlayer()
    local pGui = lp:WaitForChild("PlayerGui", 10)

    -- Remove stale GUI from previous injections
    local old = pGui:FindFirstChild("AztupUI")
    if old then old:Destroy() end

    lib.gui = create("ScreenGui", {
        Parent         = pGui,
        Name           = "AztupUI",
        ResetOnSpawn   = false,
        ZIndexBehavior = Enum.ZIndexBehavior.Sibling,
        IgnoreGuiInset = true,
    })
    return lib.gui
end

----------------------------------------------------------------------
-- NOTIFICATIONS
----------------------------------------------------------------------

local NW, NH, NP, NMX, NMY = 262, 66, 8, 16, 16

function library:Notify(data)
    data = data or {}
    local title    = data.title    or "Notification"
    local text     = data.text     or ""
    local duration = data.duration or 3

    ensureGui(self)

    local slot = #self._notifQueue + 1
    local yPos = -(NMY + (NH + NP) * slot)

    local frame = create("Frame", {
        Parent           = self.gui,
        Size             = UDim2.new(0, NW, 0, NH),
        Position         = UDim2.new(1, NW + NMX, 1, yPos),
        BackgroundColor3 = Color3.fromRGB(20, 20, 28),
        BorderSizePixel  = 0,
        ZIndex           = 50,
    })
    addCorner(frame, 8)
    create("UIStroke", { Parent = frame, Color = Color3.fromRGB(52, 52, 72), Thickness = 1, ZIndex = 50 })

    local bar = create("Frame", {
        Parent           = frame,
        Size             = UDim2.new(0, 3, 1, -14),
        Position         = UDim2.new(0, 7, 0, 7),
        BackgroundColor3 = data.accentColor or Color3.fromRGB(100, 160, 255),
        BorderSizePixel  = 0,
        ZIndex           = 51,
    })
    addCorner(bar, 2)

    create("TextLabel", {
        Parent                 = frame,
        Size                   = UDim2.new(1, -22, 0, 22),
        Position               = UDim2.new(0, 18, 0, 8),
        Text                   = title,
        TextColor3             = Color3.fromRGB(238, 238, 238),
        BackgroundTransparency = 1,
        TextXAlignment         = Enum.TextXAlignment.Left,
        Font                   = Enum.Font.GothamBold,
        TextSize               = 13,
        ZIndex                 = 51,
    })
    create("TextLabel", {
        Parent                 = frame,
        Size                   = UDim2.new(1, -22, 0, 28),
        Position               = UDim2.new(0, 18, 0, 30),
        Text                   = text,
        TextColor3             = Color3.fromRGB(172, 172, 190),
        BackgroundTransparency = 1,
        TextXAlignment         = Enum.TextXAlignment.Left,
        TextWrapped            = true,
        Font                   = Enum.Font.Gotham,
        TextSize               = 11,
        ZIndex                 = 51,
    })

    table.insert(self._notifQueue, frame)
    tween(frame, 0.3, { Position = UDim2.new(1, -(NW + NMX), 1, yPos) })

    task.delay(duration, function()
        tween(frame, 0.3, { Position = UDim2.new(1, NW + NMX, 1, yPos) })
        task.wait(0.35)
        frame:Destroy()
        for i, f in ipairs(self._notifQueue) do
            if f == frame then table.remove(self._notifQueue, i); break end
        end
        for i, f in ipairs(self._notifQueue) do
            local ny = -(NMY + (NH + NP) * i)
            tween(f, 0.22, { Position = UDim2.new(1, -(NW + NMX), 1, ny) })
        end
    end)
end

----------------------------------------------------------------------
-- WINDOW
----------------------------------------------------------------------

function library:CreateWindow(config)
    config = config or {}

    local ACCENT    = config.accent    or Color3.fromRGB(100, 160, 255)
    local BAR_COLOR = config.barColor  or Color3.fromRGB(18, 18, 24)
    local BG_COLOR  = config.bgColor   or Color3.fromRGB(26, 26, 34)
    local TXT_COLOR = config.textColor or Color3.fromRGB(238, 238, 238)
    local title     = config.title     or config.text or "Window"
    local keybind   = config.keybind
    local MAX_H     = config.maxHeight or 340

    local ELEM_BG  = Color3.fromRGB(36, 36, 50)
    local ELEM_HOV = Color3.fromRGB(46, 46, 64)
    local ELEM_H   = 28

    ensureGui(self)

    ------------------------------------------------------------------
    -- Title bar
    ------------------------------------------------------------------
    local main = create("Frame", {
        Parent           = self.gui,
        Size             = UDim2.new(0, 230, 0, 32),
        Position         = config.position or UDim2.new(0, 40, 0, 40),
        BackgroundColor3 = BAR_COLOR,
        BorderSizePixel  = 0,
        Active           = true,
        ClipsDescendants = false,
    })
    addCorner(main, 8)
    create("UIStroke", { Parent = main, Color = Color3.fromRGB(55, 55, 74), Thickness = 1 })

    create("Frame", {  -- accent strip
        Parent           = main,
        Size             = UDim2.new(1, 0, 0, 2),
        BackgroundColor3 = ACCENT,
        BorderSizePixel  = 0,
        ZIndex           = 2,
    })

    create("TextLabel", {
        Parent                 = main,
        Size                   = UDim2.new(1, -48, 1, 0),
        Position               = UDim2.new(0, 12, 0, 0),
        Text                   = title,
        TextColor3             = TXT_COLOR,
        BackgroundTransparency = 1,
        TextXAlignment         = Enum.TextXAlignment.Left,
        Font                   = Enum.Font.GothamBold,
        TextSize               = 13,
        ZIndex                 = 2,
    })

    local collapseBtn = create("TextButton", {
        Parent           = main,
        Size             = UDim2.new(0, 22, 0, 22),
        Position         = UDim2.new(1, -26, 0.5, -11),
        Text             = "-",
        TextColor3       = Color3.fromRGB(175, 175, 195),
        BackgroundColor3 = Color3.fromRGB(36, 36, 52),
        BorderSizePixel  = 0,
        Font             = Enum.Font.GothamBold,
        TextSize         = 14,
        ZIndex           = 3,
    })
    addCorner(collapseBtn, 5)

    ------------------------------------------------------------------
    -- Content container
    -- FIX: AutomaticCanvasSize removed — not supported in all
    -- environments. Canvas size is managed manually via updateCanvas().
    ------------------------------------------------------------------
    local container = create("ScrollingFrame", {
        Parent               = main,
        Size                 = UDim2.new(1, 0, 0, 0),
        Position             = UDim2.new(0, 0, 1, 4),
        BackgroundColor3     = BG_COLOR,
        BorderSizePixel      = 0,
        ClipsDescendants     = true,
        ScrollBarThickness   = 3,
        ScrollBarImageColor3 = ACCENT,
        CanvasSize           = UDim2.new(0, 0, 0, 0),
        ZIndex               = 2,
    })
    addCorner(container, 8)
    create("UIStroke", { Parent = container, Color = Color3.fromRGB(55, 55, 74), Thickness = 1 })

    local layout = create("UIListLayout", {
        Parent    = container,
        SortOrder = Enum.SortOrder.LayoutOrder,
        Padding   = UDim.new(0, 2),
    })
    addPadding(container, 6, 6)

    local collapsed = false

    local function updateCanvas()
        if collapsed then return end
        local contentH = layout.AbsoluteContentSize.Y + 14
        local h        = math.min(contentH, MAX_H)
        container.Size       = UDim2.new(1, 0, 0, h)
        container.CanvasSize = UDim2.new(0, 0, 0, layout.AbsoluteContentSize.Y + 14)
    end

    layout:GetPropertyChangedSignal("AbsoluteContentSize"):Connect(updateCanvas)
    task.defer(updateCanvas)

    ------------------------------------------------------------------
    -- Dragging
    ------------------------------------------------------------------
    local dragging, dragStart, startPos = false, nil, nil

    main.InputBegan:Connect(function(input)
        if input.UserInputType == Enum.UserInputType.MouseButton1 then
            dragging  = true
            dragStart = input.Position
            startPos  = main.Position
            input.Changed:Connect(function()
                if input.UserInputState == Enum.UserInputState.End then
                    dragging = false
                end
            end)
        end
    end)

    UIS.InputChanged:Connect(function(input)
        if dragging and input.UserInputType == Enum.UserInputType.MouseMovement then
            local d = input.Position - dragStart
            main.Position = UDim2.new(
                startPos.X.Scale, startPos.X.Offset + d.X,
                startPos.Y.Scale, startPos.Y.Offset + d.Y
            )
        end
    end)

    UIS.InputEnded:Connect(function(input)
        if input.UserInputType == Enum.UserInputType.MouseButton1 then
            dragging = false
        end
    end)

    ------------------------------------------------------------------
    -- Collapse / expand
    ------------------------------------------------------------------
    collapseBtn.MouseButton1Click:Connect(function()
        collapsed = not collapsed
        if collapsed then
            tween(container, 0.2, { Size = UDim2.new(1, 0, 0, 0) })
            collapseBtn.Text = "+"
        else
            collapseBtn.Text = "-"
            local h = math.min(layout.AbsoluteContentSize.Y + 14, MAX_H)
            tween(container, 0.2, { Size = UDim2.new(1, 0, 0, h) })
        end
    end)

    if keybind then
        UIS.InputBegan:Connect(function(input, gpe)
            if not gpe and input.KeyCode == keybind then
                main.Visible = not main.Visible
            end
        end)
    end

    ------------------------------------------------------------------
    -- Shared helpers
    ------------------------------------------------------------------

    local function baseElem(h)
        local f = create("Frame", {
            Parent           = container,
            Size             = UDim2.new(1, 0, 0, h or ELEM_H),
            BackgroundColor3 = ELEM_BG,
            BorderSizePixel  = 0,
        })
        addCorner(f, 5)
        return f
    end

    -- FIX: hover connected to the overlay BUTTON, not the frame.
    -- The overlay absorbs all mouse events so MouseEnter on the frame
    -- never fires — must wire hover through the button instead.
    local function applyHover(btn, frame)
        btn.MouseEnter:Connect(function() tween(frame, 0.1, { BackgroundColor3 = ELEM_HOV }) end)
        btn.MouseLeave:Connect(function() tween(frame, 0.1, { BackgroundColor3 = ELEM_BG  }) end)
    end

    -- Transparent full-size click overlay (ZIndex 5 = above labels/tracks)
    local function overlay(parent)
        return create("TextButton", {
            Parent                 = parent,
            Size                   = UDim2.new(1, 0, 1, 0),
            Text                   = "",
            BackgroundTransparency = 1,
            ZIndex                 = 5,
        })
    end

    ------------------------------------------------------------------
    -- Window object
    ------------------------------------------------------------------
    local window = { _main = main, _container = container }

    ----------------------------------------------------------------
    -- LABEL
    ----------------------------------------------------------------
    function window:Label(text)
        local f = baseElem(22)
        f.BackgroundTransparency = 1
        create("TextLabel", {
            Parent                 = f,
            Size                   = UDim2.new(1, -10, 1, 0),
            Position               = UDim2.new(0, 8, 0, 0),
            Text                   = text,
            TextColor3             = Color3.fromRGB(148, 148, 170),
            BackgroundTransparency = 1,
            TextXAlignment         = Enum.TextXAlignment.Left,
            Font                   = Enum.Font.Gotham,
            TextSize               = 11,
            ZIndex                 = 3,
        })
    end

    ----------------------------------------------------------------
    -- SEPARATOR
    ----------------------------------------------------------------
    function window:Separator(text)
        local f = create("Frame", {
            Parent                 = container,
            Size                   = UDim2.new(1, 0, 0, 20),
            BackgroundTransparency = 1,
            BorderSizePixel        = 0,
        })
        create("Frame", {
            Parent           = f,
            Size             = UDim2.new(1, -10, 0, 1),
            Position         = UDim2.new(0, 5, 0.5, 0),
            BackgroundColor3 = Color3.fromRGB(55, 55, 74),
            BorderSizePixel  = 0,
        })
        if text and text ~= "" then
            create("TextLabel", {
                Parent           = f,
                AutomaticSize    = Enum.AutomaticSize.X,
                Size             = UDim2.new(0, 0, 1, 0),
                Position         = UDim2.new(0.5, 0, 0, 0),
                AnchorPoint      = Vector2.new(0.5, 0),
                Text             = "  " .. text .. "  ",
                TextColor3       = Color3.fromRGB(120, 120, 150),
                BackgroundColor3 = BG_COLOR,
                BorderSizePixel  = 0,
                Font             = Enum.Font.GothamBold,
                TextSize         = 10,
                ZIndex           = 2,
            })
        end
    end

    ----------------------------------------------------------------
    -- BUTTON
    ----------------------------------------------------------------
    function window:Button(text, callback)
        local f   = baseElem(ELEM_H)
        local btn = create("TextButton", {
            Parent                 = f,
            Size                   = UDim2.new(1, 0, 1, 0),
            Text                   = text,
            TextColor3             = Color3.fromRGB(212, 212, 228),
            BackgroundTransparency = 1,
            Font                   = Enum.Font.Gotham,
            TextSize               = 12,
            ZIndex                 = 3,
        })
        applyHover(btn, f)
        btn.MouseButton1Click:Connect(function()
            tween(f, 0.07, { BackgroundColor3 = ACCENT })
            tween(f, 0.2,  { BackgroundColor3 = ELEM_BG })
            pcall(callback)
        end)
    end

    ----------------------------------------------------------------
    -- TOGGLE
    -- FIX v2: renamed visibility helper to ToggleVisible() so this
    -- function is never overwritten (was the root cause of toggles
    -- being invisible — the second definition erased this one).
    -- FIX v3: hover wired through overlay button, not frame.
    ----------------------------------------------------------------
    function window:Toggle(text, default, callback)
        if type(default) == "function" then
            callback = default; default = false
        end
        local state = (default == true)

        local f = baseElem(ELEM_H)

        create("TextLabel", {
            Parent                 = f,
            Size                   = UDim2.new(1, -54, 1, 0),
            Position               = UDim2.new(0, 8, 0, 0),
            Text                   = text,
            TextColor3             = Color3.fromRGB(212, 212, 228),
            BackgroundTransparency = 1,
            TextXAlignment         = Enum.TextXAlignment.Left,
            Font                   = Enum.Font.Gotham,
            TextSize               = 12,
            ZIndex                 = 3,
        })

        -- Pill track
        local track = create("Frame", {
            Parent           = f,
            Size             = UDim2.new(0, 36, 0, 18),
            Position         = UDim2.new(1, -44, 0.5, -9),
            BackgroundColor3 = state and ACCENT or Color3.fromRGB(50, 50, 68),
            BorderSizePixel  = 0,
            ZIndex           = 3,
        })
        addCorner(track, 9)

        -- Thumb
        local thumb = create("Frame", {
            Parent           = track,
            Size             = UDim2.new(0, 13, 0, 13),
            Position         = state
                and UDim2.new(1, -16, 0.5, -6)
                or  UDim2.new(0,   3, 0.5, -6),
            BackgroundColor3 = Color3.fromRGB(255, 255, 255),
            BorderSizePixel  = 0,
            ZIndex           = 4,
        })
        addCorner(thumb, 7)

        local ov = overlay(f)
        applyHover(ov, f)

        local function refresh()
            tween(track, 0.15, { BackgroundColor3 = state and ACCENT or Color3.fromRGB(50, 50, 68) })
            tween(thumb, 0.15, {
                Position = state
                    and UDim2.new(1, -16, 0.5, -6)
                    or  UDim2.new(0,   3, 0.5, -6),
            })
        end

        ov.MouseButton1Click:Connect(function()
            state = not state
            refresh()
            pcall(callback, state)
        end)

        return {
            SetState = function(_, s) state = s; refresh() end,
            GetState = function()     return state          end,
        }
    end

    ----------------------------------------------------------------
    -- SLIDER
    ----------------------------------------------------------------
    function window:Slider(text, min, max, default, callback)
        if type(default) == "function" then
            callback = default; default = min
        end
        local value = math.clamp(default or min, min, max)

        local f = baseElem(44)

        create("TextLabel", {
            Parent                 = f,
            Size                   = UDim2.new(1, -54, 0, 18),
            Position               = UDim2.new(0, 8, 0, 4),
            Text                   = text,
            TextColor3             = Color3.fromRGB(212, 212, 228),
            BackgroundTransparency = 1,
            TextXAlignment         = Enum.TextXAlignment.Left,
            Font                   = Enum.Font.Gotham,
            TextSize               = 12,
            ZIndex                 = 3,
        })

        local valLbl = create("TextLabel", {
            Parent                 = f,
            Size                   = UDim2.new(0, 44, 0, 18),
            Position               = UDim2.new(1, -52, 0, 4),
            Text                   = tostring(value),
            TextColor3             = ACCENT,
            BackgroundTransparency = 1,
            TextXAlignment         = Enum.TextXAlignment.Right,
            Font                   = Enum.Font.GothamBold,
            TextSize               = 12,
            ZIndex                 = 3,
        })

        local track = create("Frame", {
            Parent           = f,
            Size             = UDim2.new(1, -16, 0, 5),
            Position         = UDim2.new(0, 8, 1, -13),
            BackgroundColor3 = Color3.fromRGB(46, 46, 64),
            BorderSizePixel  = 0,
            ZIndex           = 3,
        })
        addCorner(track, 3)

        local fill = create("Frame", {
            Parent           = track,
            Size             = UDim2.new((value - min) / (max - min), 0, 1, 0),
            BackgroundColor3 = ACCENT,
            BorderSizePixel  = 0,
            ZIndex           = 4,
        })
        addCorner(fill, 3)

        local dragZone = create("TextButton", {
            Parent                 = track,
            Size                   = UDim2.new(1, 0, 0, 24),
            Position               = UDim2.new(0, 0, 0.5, -12),
            Text                   = "",
            BackgroundTransparency = 1,
            ZIndex                 = 5,
        })

        local sliding = false

        local function applyPos(ix)
            local rel = math.clamp(ix - track.AbsolutePosition.X, 0, track.AbsoluteSize.X)
            local pct = rel / track.AbsoluteSize.X
            value       = math.floor(min + (max - min) * pct + 0.5)
            fill.Size   = UDim2.new(pct, 0, 1, 0)
            valLbl.Text = tostring(value)
            pcall(callback, value)
        end

        dragZone.MouseButton1Down:Connect(function() sliding = true end)
        UIS.InputChanged:Connect(function(i)
            if sliding and i.UserInputType == Enum.UserInputType.MouseMovement then
                applyPos(i.Position.X)
            end
        end)
        UIS.InputEnded:Connect(function(i)
            if i.UserInputType == Enum.UserInputType.MouseButton1 then sliding = false end
        end)

        return {
            SetValue = function(_, v)
                value = math.clamp(v, min, max)
                fill.Size   = UDim2.new((value - min) / (max - min), 0, 1, 0)
                valLbl.Text = tostring(value)
            end,
            GetValue = function() return value end,
        }
    end

    ----------------------------------------------------------------
    -- DROPDOWN
    ----------------------------------------------------------------
    function window:Dropdown(text, options, callback)
        options = options or {}
        local selected = nil
        local isOpen   = false

        local f = baseElem(ELEM_H)

        create("TextLabel", {
            Parent                 = f,
            Size                   = UDim2.new(0.55, 0, 1, 0),
            Position               = UDim2.new(0, 8, 0, 0),
            Text                   = text,
            TextColor3             = Color3.fromRGB(212, 212, 228),
            BackgroundTransparency = 1,
            TextXAlignment         = Enum.TextXAlignment.Left,
            Font                   = Enum.Font.Gotham,
            TextSize               = 12,
            ZIndex                 = 3,
        })

        local selLbl = create("TextLabel", {
            Parent                 = f,
            Size                   = UDim2.new(0.38, 0, 1, 0),
            Position               = UDim2.new(0.58, 0, 0, 0),
            Text                   = "Select...",
            TextColor3             = Color3.fromRGB(115, 115, 142),
            BackgroundTransparency = 1,
            TextXAlignment         = Enum.TextXAlignment.Right,
            Font                   = Enum.Font.Gotham,
            TextSize               = 11,
            ZIndex                 = 3,
        })

        local arrow = create("TextLabel", {
            Parent                 = f,
            Size                   = UDim2.new(0, 16, 1, 0),
            Position               = UDim2.new(1, -18, 0, 0),
            Text                   = "v",
            TextColor3             = Color3.fromRGB(115, 115, 142),
            BackgroundTransparency = 1,
            Font                   = Enum.Font.GothamBold,
            TextSize               = 11,
            ZIndex                 = 3,
        })

        -- Panel parented to main so it floats above the container
        local panel = create("Frame", {
            Parent           = main,
            Size             = UDim2.new(0, 218, 0, 0),
            BackgroundColor3 = Color3.fromRGB(26, 26, 40),
            BorderSizePixel  = 0,
            Visible          = false,
            ZIndex           = 20,
            ClipsDescendants = true,
        })
        addCorner(panel, 6)
        create("UIStroke", { Parent = panel, Color = Color3.fromRGB(55, 55, 74), Thickness = 1, ZIndex = 20 })

        local pLayout = create("UIListLayout", {
            Parent    = panel,
            SortOrder = Enum.SortOrder.LayoutOrder,
            Padding   = UDim.new(0, 2),
        })
        addPadding(panel, 4, 4)

        local function closePanel()
            isOpen = false
            tween(panel, 0.14, { Size = UDim2.new(0, 218, 0, 0) })
            task.delay(0.15, function() panel.Visible = false end)
            arrow.Text = "v"
        end

        for _, opt in ipairs(options) do
            local row = create("TextButton", {
                Parent           = panel,
                Size             = UDim2.new(1, 0, 0, 24),
                Text             = opt,
                TextColor3       = Color3.fromRGB(202, 202, 222),
                BackgroundColor3 = Color3.fromRGB(32, 32, 48),
                BorderSizePixel  = 0,
                Font             = Enum.Font.Gotham,
                TextSize         = 11,
                ZIndex           = 21,
            })
            addCorner(row, 4)
            row.MouseEnter:Connect(function() tween(row, 0.1, { BackgroundColor3 = Color3.fromRGB(46, 46, 66) }) end)
            row.MouseLeave:Connect(function() tween(row, 0.1, { BackgroundColor3 = Color3.fromRGB(32, 32, 48) }) end)
            row.MouseButton1Click:Connect(function()
                selected          = opt
                selLbl.Text       = opt
                selLbl.TextColor3 = Color3.fromRGB(198, 198, 218)
                closePanel()
                pcall(callback, opt)
            end)
        end

        local ov = overlay(f)
        applyHover(ov, f)

        ov.MouseButton1Click:Connect(function()
            if isOpen then
                closePanel()
            else
                isOpen = true
                local relY = f.AbsolutePosition.Y - main.AbsolutePosition.Y
                panel.Position = UDim2.new(0, 6, 0, relY + ELEM_H + 2)
                panel.Visible  = true
                local th = math.min(pLayout.AbsoluteContentSize.Y + 10, 160)
                tween(panel, 0.15, { Size = UDim2.new(0, 218, 0, th) })
                arrow.Text = "^"
            end
        end)

        return {
            SetSelected = function(_, v) selected = v; selLbl.Text = v end,
            GetSelected = function() return selected end,
        }
    end

    ----------------------------------------------------------------
    -- TEXTBOX
    ----------------------------------------------------------------
    function window:TextBox(placeholder, callback)
        local f = baseElem(ELEM_H)

        local box = create("TextBox", {
            Parent                 = f,
            Size                   = UDim2.new(1, -10, 1, -6),
            Position               = UDim2.new(0, 5, 0, 3),
            PlaceholderText        = placeholder or "Type here...",
            Text                   = "",
            TextColor3             = Color3.fromRGB(212, 212, 228),
            PlaceholderColor3      = Color3.fromRGB(100, 100, 126),
            BackgroundTransparency = 1,
            Font                   = Enum.Font.Gotham,
            TextSize               = 12,
            TextXAlignment         = Enum.TextXAlignment.Left,
            ClearTextOnFocus       = false,
            ZIndex                 = 3,
        })

        box.FocusLost:Connect(function(enter)
            if enter then pcall(callback, box.Text) end
        end)
        box.Focused:Connect(function()   tween(f, 0.1, { BackgroundColor3 = ELEM_HOV }) end)
        box.FocusLost:Connect(function() tween(f, 0.1, { BackgroundColor3 = ELEM_BG  }) end)

        return {
            GetText = function()     return box.Text end,
            SetText = function(_, t) box.Text = t   end,
            Clear   = function()     box.Text = ""  end,
        }
    end

    ----------------------------------------------------------------
    -- COLORPICKER
    ----------------------------------------------------------------
    function window:ColorPicker(text, default, callback)
        default = default or Color3.fromRGB(255, 100, 100)
        local currentColor = default

        local f = baseElem(ELEM_H)

        create("TextLabel", {
            Parent                 = f,
            Size                   = UDim2.new(1, -52, 1, 0),
            Position               = UDim2.new(0, 8, 0, 0),
            Text                   = text,
            TextColor3             = Color3.fromRGB(212, 212, 228),
            BackgroundTransparency = 1,
            TextXAlignment         = Enum.TextXAlignment.Left,
            Font                   = Enum.Font.Gotham,
            TextSize               = 12,
            ZIndex                 = 3,
        })

        local swatch = create("Frame", {
            Parent           = f,
            Size             = UDim2.new(0, 22, 0, 16),
            Position         = UDim2.new(1, -30, 0.5, -8),
            BackgroundColor3 = default,
            BorderSizePixel  = 0,
            ZIndex           = 3,
        })
        addCorner(swatch, 4)
        create("UIStroke", { Parent = swatch, Color = Color3.fromRGB(80, 80, 104), Thickness = 1, ZIndex = 4 })

        -- Preset palette panel (inline in container)
        local panel = create("Frame", {
            Parent           = container,
            Size             = UDim2.new(1, 0, 0, 0),
            BackgroundColor3 = Color3.fromRGB(30, 30, 46),
            BorderSizePixel  = 0,
            ClipsDescendants = true,
            Visible          = false,
        })
        addCorner(panel, 5)

        local presets = {
            Color3.fromRGB(255,70,70),  Color3.fromRGB(255,150,45),
            Color3.fromRGB(248,212,45), Color3.fromRGB(70,210,115),
            Color3.fromRGB(70,170,255), Color3.fromRGB(150,90,255),
            Color3.fromRGB(255,90,170), Color3.fromRGB(255,255,255),
        }

        local row = create("Frame", {
            Parent                 = panel,
            Size                   = UDim2.new(1, -12, 0, 26),
            Position               = UDim2.new(0, 6, 0, 6),
            BackgroundTransparency = 1,
        })
        create("UIListLayout", {
            Parent        = row,
            FillDirection = Enum.FillDirection.Horizontal,
            Padding       = UDim.new(0, 5),
        })

        for _, c in ipairs(presets) do
            local dot = create("TextButton", {
                Parent           = row,
                Size             = UDim2.new(0, 22, 0, 22),
                Text             = "",
                BackgroundColor3 = c,
                BorderSizePixel  = 0,
                ZIndex           = 3,
            })
            addCorner(dot, 5)
            dot.MouseButton1Click:Connect(function()
                currentColor            = c
                swatch.BackgroundColor3 = c
                pcall(callback, c)
            end)
        end

        local isOpen = false
        local ov = overlay(f)
        applyHover(ov, f)

        ov.MouseButton1Click:Connect(function()
            isOpen = not isOpen
            if isOpen then
                panel.Visible = true
                tween(panel, 0.15, { Size = UDim2.new(1, 0, 0, 40) })
            else
                tween(panel, 0.13, { Size = UDim2.new(1, 0, 0, 0) })
                task.delay(0.14, function() panel.Visible = false end)
            end
        end)

        return {
            SetColor = function(_, c) currentColor = c; swatch.BackgroundColor3 = c end,
            GetColor = function()     return currentColor end,
        }
    end

    ----------------------------------------------------------------
    -- Visibility
    -- NOTE: ToggleVisible (NOT Toggle) — keeping Toggle free for the
    -- element builder above so it is never overwritten.
    ----------------------------------------------------------------
    function window:Show()          main.Visible = true             end
    function window:Hide()          main.Visible = false            end
    function window:ToggleVisible() main.Visible = not main.Visible end
    function window:Destroy()       main:Destroy()                  end

    table.insert(library.windows, window)
    return window
end

----------------------------------------------------------------------
-- Destroy everything
----------------------------------------------------------------------
function library:Destroy()
    if self.gui then self.gui:Destroy(); self.gui = nil end
    self.windows     = {}
    self._notifQueue = {}
end

return library

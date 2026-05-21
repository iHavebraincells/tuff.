--// Aztup UI Library (Rewritten & Fixed v2)
--// ROOT-CAUSE FIX: window:Toggle() visibility helper overwrote window:Toggle() element.
--// Renamed visibility helper to window:ToggleVisible().
--// Also fixed: hover not firing on toggle (btn overlay absorbed mouse events),
--//             slider ZIndex, dropdown panel positioning, container sizing.

local Players      = game:GetService("Players")
local UIS          = game:GetService("UserInputService")
local TweenService = game:GetService("TweenService")
local LocalPlayer  = Players.LocalPlayer

----------------------------------------------------------------------
-- Library table
----------------------------------------------------------------------
local library = {
    windows      = {},
    gui          = nil,
    _notifQueue  = {},
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

local function ensureGui(lib)
    if not lib.gui or not lib.gui.Parent then
        lib.gui = create("ScreenGui", {
            Parent         = LocalPlayer:WaitForChild("PlayerGui"),
            Name           = "AztupUI",
            ResetOnSpawn   = false,
            ZIndexBehavior = Enum.ZIndexBehavior.Sibling,
            IgnoreGuiInset = true,
        })
    end
    return lib.gui
end

----------------------------------------------------------------------
-- NOTIFICATIONS
----------------------------------------------------------------------

local NOTIF_W  = 260
local NOTIF_H  = 65
local NOTIF_P  = 8
local NOTIF_MX = 16
local NOTIF_MY = 16

function library:Notify(data)
    data = data or {}
    local title    = data.title    or "Notification"
    local text     = data.text     or ""
    local duration = data.duration or 3

    ensureGui(self)

    local slot = #self._notifQueue + 1
    local yPos = -(NOTIF_MY + (NOTIF_H + NOTIF_P) * slot)

    local frame = create("Frame", {
        Parent           = self.gui,
        Size             = UDim2.new(0, NOTIF_W, 0, NOTIF_H),
        Position         = UDim2.new(1, NOTIF_W + NOTIF_MX, 1, yPos),
        BackgroundColor3 = Color3.fromRGB(22, 22, 28),
        BorderSizePixel  = 0,
        ZIndex           = 50,
    })
    addCorner(frame, 8)
    create("UIStroke", { Parent = frame, Color = Color3.fromRGB(50,50,70), Thickness = 1, ZIndex = 50 })

    local accentBar = create("Frame", {
        Parent           = frame,
        Size             = UDim2.new(0, 3, 1, -14),
        Position         = UDim2.new(0, 7, 0, 7),
        BackgroundColor3 = data.accentColor or Color3.fromRGB(100, 160, 255),
        BorderSizePixel  = 0,
        ZIndex           = 51,
    })
    addCorner(accentBar, 2)

    create("TextLabel", {
        Parent                 = frame,
        Size                   = UDim2.new(1, -22, 0, 22),
        Position               = UDim2.new(0, 18, 0, 8),
        Text                   = title,
        TextColor3             = Color3.fromRGB(240, 240, 240),
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
        TextColor3             = Color3.fromRGB(175, 175, 190),
        BackgroundTransparency = 1,
        TextXAlignment         = Enum.TextXAlignment.Left,
        TextWrapped            = true,
        Font                   = Enum.Font.Gotham,
        TextSize               = 11,
        ZIndex                 = 51,
    })

    table.insert(self._notifQueue, frame)
    tween(frame, 0.3, { Position = UDim2.new(1, -(NOTIF_W + NOTIF_MX), 1, yPos) })

    task.delay(duration, function()
        tween(frame, 0.3, { Position = UDim2.new(1, NOTIF_W + NOTIF_MX, 1, yPos) })
        task.wait(0.35)
        frame:Destroy()
        for i, f in ipairs(self._notifQueue) do
            if f == frame then table.remove(self._notifQueue, i) break end
        end
        for i, f in ipairs(self._notifQueue) do
            local ny = -(NOTIF_MY + (NOTIF_H + NOTIF_P) * i)
            tween(f, 0.22, { Position = UDim2.new(1, -(NOTIF_W + NOTIF_MX), 1, ny) })
        end
    end)
end

----------------------------------------------------------------------
-- WINDOW
----------------------------------------------------------------------

function library:CreateWindow(config)
    config = config or {}

    local ACCENT    = config.accent   or Color3.fromRGB(100, 160, 255)
    local BAR_COLOR = config.barColor or Color3.fromRGB(18, 18, 24)
    local BG_COLOR  = config.bgColor  or Color3.fromRGB(26, 26, 34)
    local TXT_COLOR = config.textColor or Color3.fromRGB(240, 240, 240)
    local title     = config.title    or config.text or "Window"
    local keybind   = config.keybind  or nil

    -- Element colours (shared across all element builders)
    local ELEM_BG     = Color3.fromRGB(36, 36, 48)
    local ELEM_HOV    = Color3.fromRGB(46, 46, 62)
    local ELEM_H      = 28
    local MAX_H       = config.maxHeight or 340

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
    create("UIStroke", { Parent = main, Color = Color3.fromRGB(55, 55, 72), Thickness = 1 })

    -- Accent strip at top
    local strip = create("Frame", {
        Parent           = main,
        Size             = UDim2.new(1, 0, 0, 2),
        BackgroundColor3 = ACCENT,
        BorderSizePixel  = 0,
        ZIndex           = 2,
    })
    addCorner(strip, 2)

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
        Text             = "−",
        TextColor3       = Color3.fromRGB(180, 180, 195),
        BackgroundColor3 = Color3.fromRGB(38, 38, 52),
        BorderSizePixel  = 0,
        Font             = Enum.Font.GothamBold,
        TextSize         = 14,
        ZIndex           = 3,
    })
    addCorner(collapseBtn, 5)

    ------------------------------------------------------------------
    -- Content container
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
        AutomaticCanvasSize  = Enum.AutomaticSize.Y,
        ZIndex               = 2,
    })
    addCorner(container, 8)
    create("UIStroke", { Parent = container, Color = Color3.fromRGB(55, 55, 72), Thickness = 1 })

    local layout = create("UIListLayout", {
        Parent    = container,
        SortOrder = Enum.SortOrder.LayoutOrder,
        Padding   = UDim.new(0, 2),
    })
    addPadding(container, 6, 6)

    -- Keep container height capped
    local function refreshHeight()
        local h = math.min(layout.AbsoluteContentSize.Y + 14, MAX_H)
        container.Size = UDim2.new(1, 0, 0, h)
    end
    layout:GetPropertyChangedSignal("AbsoluteContentSize"):Connect(refreshHeight)
    task.defer(refreshHeight)

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
    -- Collapse
    ------------------------------------------------------------------
    local collapsed = false

    collapseBtn.MouseButton1Click:Connect(function()
        collapsed = not collapsed
        if collapsed then
            tween(container, 0.22, { Size = UDim2.new(1, 0, 0, 0) })
            collapseBtn.Text = "+"
        else
            local h = math.min(layout.AbsoluteContentSize.Y + 14, MAX_H)
            tween(container, 0.22, { Size = UDim2.new(1, 0, 0, h) })
            collapseBtn.Text = "−"
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

    -- Base element frame parented to container
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

    -- Hover: connect to the BUTTON (btn) but change FRAME (f) colour.
    -- This is needed because a full-size btn overlay absorbs mouse events.
    local function applyHover(btn, f)
        btn.MouseEnter:Connect(function() tween(f, 0.1, { BackgroundColor3 = ELEM_HOV }) end)
        btn.MouseLeave:Connect(function() tween(f, 0.1, { BackgroundColor3 = ELEM_BG  }) end)
    end

    -- Full-size transparent click overlay that sits on top of all children in f
    local function makeOverlay(f)
        return create("TextButton", {
            Parent                 = f,
            Size                   = UDim2.new(1, 0, 1, 0),
            Text                   = "",
            BackgroundTransparency = 1,
            ZIndex                 = 5,   -- above label, track, etc.
        })
    end

    ------------------------------------------------------------------
    -- Window element table
    ------------------------------------------------------------------
    local window = { _main = main, _container = container }

    ----------------------------------------------------------------
    -- LABEL
    ----------------------------------------------------------------
    function window:Label(text)
        local f = baseElem(22)
        f.BackgroundTransparency = 1   -- labels have no background
        create("TextLabel", {
            Parent                 = f,
            Size                   = UDim2.new(1, -10, 1, 0),
            Position               = UDim2.new(0, 8, 0, 0),
            Text                   = text,
            TextColor3             = Color3.fromRGB(155, 155, 175),
            BackgroundTransparency = 1,
            TextXAlignment         = Enum.TextXAlignment.Left,
            Font                   = Enum.Font.Gotham,
            TextSize               = 11,
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
            BackgroundColor3 = Color3.fromRGB(55, 55, 72),
            BorderSizePixel  = 0,
        })
        if text and text ~= "" then
            create("TextLabel", {
                Parent                 = f,
                AutomaticSize          = Enum.AutomaticSize.X,
                Size                   = UDim2.new(0, 0, 1, 0),
                Position               = UDim2.new(0.5, 0, 0, 0),
                AnchorPoint            = Vector2.new(0.5, 0),
                Text                   = "  " .. text .. "  ",
                TextColor3             = Color3.fromRGB(125, 125, 155),
                BackgroundColor3       = BG_COLOR,
                BorderSizePixel        = 0,
                Font                   = Enum.Font.GothamBold,
                TextSize               = 10,
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
            TextColor3             = Color3.fromRGB(215, 215, 230),
            BackgroundTransparency = 1,
            Font                   = Enum.Font.Gotham,
            TextSize               = 12,
            ZIndex                 = 3,
        })
        applyHover(btn, f)

        btn.MouseButton1Click:Connect(function()
            tween(f, 0.07, { BackgroundColor3 = ACCENT })
            tween(f, 0.18, { BackgroundColor3 = ELEM_BG })
            pcall(callback)
        end)
    end

    ----------------------------------------------------------------
    -- TOGGLE
    -- FIX: was named window:Toggle() which collided with the visibility
    --      helper of the same name defined below, erasing this function.
    --      Visibility helper is now window:ToggleVisible().
    --      Also fixed: hover now connected to the overlay btn, not f.
    ----------------------------------------------------------------
    function window:Toggle(text, default, callback)
        -- Support old 2-arg style:  Toggle(text, callback)
        if type(default) == "function" then
            callback = default
            default  = false
        end
        local state = (default == true)

        local f = baseElem(ELEM_H)

        -- Label
        create("TextLabel", {
            Parent                 = f,
            Size                   = UDim2.new(1, -54, 1, 0),
            Position               = UDim2.new(0, 8, 0, 0),
            Text                   = text,
            TextColor3             = Color3.fromRGB(215, 215, 230),
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
            BackgroundColor3 = state and ACCENT or Color3.fromRGB(52, 52, 68),
            BorderSizePixel  = 0,
            ZIndex           = 3,
        })
        addCorner(track, 9)

        -- Thumb
        local thumb = create("Frame", {
            Parent           = track,
            Size             = UDim2.new(0, 13, 0, 13),
            Position         = state and UDim2.new(1, -16, 0.5, -6.5) or UDim2.new(0, 3, 0.5, -6.5),
            BackgroundColor3 = Color3.fromRGB(255, 255, 255),
            BorderSizePixel  = 0,
            ZIndex           = 4,
        })
        addCorner(thumb, 7)

        -- Transparent overlay for clicks (ZIndex 5 = on top)
        local overlay = makeOverlay(f)
        applyHover(overlay, f)

        local function setVisual()
            tween(track, 0.16, { BackgroundColor3 = state and ACCENT or Color3.fromRGB(52, 52, 68) })
            tween(thumb, 0.16, {
                Position = state
                    and UDim2.new(1, -16, 0.5, -6.5)
                    or  UDim2.new(0,  3, 0.5, -6.5)
            })
        end
        setVisual()

        overlay.MouseButton1Click:Connect(function()
            state = not state
            setVisual()
            pcall(callback, state)
        end)

        return {
            SetState = function(_, s) state = s; setVisual() end,
            GetState = function() return state end,
        }
    end

    ----------------------------------------------------------------
    -- SLIDER
    ----------------------------------------------------------------
    function window:Slider(text, min, max, default, callback)
        if type(default) == "function" then
            callback = default
            default  = min
        end
        local value = math.clamp(default or min, min, max)

        local f = baseElem(44)

        create("TextLabel", {
            Parent                 = f,
            Size                   = UDim2.new(1, -54, 0, 18),
            Position               = UDim2.new(0, 8, 0, 4),
            Text                   = text,
            TextColor3             = Color3.fromRGB(215, 215, 230),
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

        -- Track
        local track = create("Frame", {
            Parent           = f,
            Size             = UDim2.new(1, -16, 0, 5),
            Position         = UDim2.new(0, 8, 1, -13),
            BackgroundColor3 = Color3.fromRGB(48, 48, 64),
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

        -- Drag zone over the track
        local dragZone = create("TextButton", {
            Parent                 = track,
            Size                   = UDim2.new(1, 0, 0, 24),
            Position               = UDim2.new(0, 0, 0.5, -12),
            Text                   = "",
            BackgroundTransparency = 1,
            ZIndex                 = 5,
        })

        local sliding = false

        local function applyPos(inputPos)
            local rel = math.clamp(inputPos.X - track.AbsolutePosition.X, 0, track.AbsoluteSize.X)
            local pct = rel / track.AbsoluteSize.X
            value        = math.floor(min + (max - min) * pct + 0.5)
            fill.Size    = UDim2.new(pct, 0, 1, 0)
            valLbl.Text  = tostring(value)
            pcall(callback, value)
        end

        dragZone.MouseButton1Down:Connect(function() sliding = true end)

        UIS.InputChanged:Connect(function(i)
            if sliding and i.UserInputType == Enum.UserInputType.MouseMovement then
                applyPos(i.Position)
            end
        end)
        UIS.InputEnded:Connect(function(i)
            if i.UserInputType == Enum.UserInputType.MouseButton1 then
                sliding = false
            end
        end)

        return {
            SetValue = function(_, v)
                value = math.clamp(v, min, max)
                local pct   = (value - min) / (max - min)
                fill.Size   = UDim2.new(pct, 0, 1, 0)
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

        local f = baseElem(ELEM_H)

        create("TextLabel", {
            Parent                 = f,
            Size                   = UDim2.new(0.55, 0, 1, 0),
            Position               = UDim2.new(0, 8, 0, 0),
            Text                   = text,
            TextColor3             = Color3.fromRGB(215, 215, 230),
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
            TextColor3             = Color3.fromRGB(120, 120, 145),
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
            Text                   = "▾",
            TextColor3             = Color3.fromRGB(120, 120, 145),
            BackgroundTransparency = 1,
            Font                   = Enum.Font.Gotham,
            TextSize               = 12,
            ZIndex                 = 3,
        })

        -- Dropdown panel parented to main (so it can float above the container)
        local panel = create("Frame", {
            Parent           = main,
            Size             = UDim2.new(0, 218, 0, 0),
            BackgroundColor3 = Color3.fromRGB(28, 28, 40),
            BorderSizePixel  = 0,
            Visible          = false,
            ZIndex           = 20,
            ClipsDescendants = true,
        })
        addCorner(panel, 6)
        create("UIStroke", { Parent = panel, Color = Color3.fromRGB(55, 55, 72), Thickness = 1, ZIndex = 20 })

        local pLayout = create("UIListLayout", {
            Parent    = panel,
            SortOrder = Enum.SortOrder.LayoutOrder,
            Padding   = UDim.new(0, 2),
        })
        addPadding(panel, 4, 4)

        local function closePanel(open)
            tween(panel, 0.15, { Size = UDim2.new(0, 218, 0, 0) })
            task.delay(0.16, function() panel.Visible = false end)
            tween(arrow, 0.14, { Rotation = 0 })
            return false
        end

        local open = false

        for _, opt in ipairs(options) do
            local row = create("TextButton", {
                Parent           = panel,
                Size             = UDim2.new(1, 0, 0, 24),
                Text             = opt,
                TextColor3       = Color3.fromRGB(205, 205, 225),
                BackgroundColor3 = Color3.fromRGB(34, 34, 48),
                BorderSizePixel  = 0,
                Font             = Enum.Font.Gotham,
                TextSize         = 11,
                ZIndex           = 21,
            })
            addCorner(row, 4)
            row.MouseEnter:Connect(function() tween(row, 0.1, { BackgroundColor3 = Color3.fromRGB(48, 48, 66) }) end)
            row.MouseLeave:Connect(function() tween(row, 0.1, { BackgroundColor3 = Color3.fromRGB(34, 34, 48) }) end)
            row.MouseButton1Click:Connect(function()
                selected = opt
                selLbl.Text      = opt
                selLbl.TextColor3 = Color3.fromRGB(200, 200, 220)
                open = closePanel()
                pcall(callback, opt)
            end)
        end

        local overlay = makeOverlay(f)
        applyHover(overlay, f)

        overlay.MouseButton1Click:Connect(function()
            open = not open
            if open then
                local relY = f.AbsolutePosition.Y - main.AbsolutePosition.Y
                panel.Position = UDim2.new(0, 6, 0, relY + ELEM_H + 2)
                panel.Visible  = true
                local th = math.min(pLayout.AbsoluteContentSize.Y + 10, 160)
                tween(panel, 0.16, { Size = UDim2.new(0, 218, 0, th) })
                tween(arrow, 0.14, { Rotation = 180 })
            else
                open = closePanel()
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
            TextColor3             = Color3.fromRGB(215, 215, 230),
            PlaceholderColor3      = Color3.fromRGB(105, 105, 130),
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
            GetText = function()    return box.Text end,
            SetText = function(_, t) box.Text = t  end,
            Clear   = function()    box.Text = ""  end,
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
            TextColor3             = Color3.fromRGB(215, 215, 230),
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
        create("UIStroke", { Parent = swatch, Color = Color3.fromRGB(80,80,100), Thickness = 1, ZIndex = 4 })

        -- Preset panel (inline in container)
        local panel = create("Frame", {
            Parent           = container,
            Size             = UDim2.new(1, 0, 0, 0),
            BackgroundColor3 = Color3.fromRGB(30, 30, 44),
            BorderSizePixel  = 0,
            ClipsDescendants = true,
            Visible          = false,
        })
        addCorner(panel, 5)

        local presets = {
            Color3.fromRGB(255,75,75),   Color3.fromRGB(255,155,50),
            Color3.fromRGB(250,215,50),  Color3.fromRGB(75,215,120),
            Color3.fromRGB(75,175,255),  Color3.fromRGB(155,95,255),
            Color3.fromRGB(255,95,175),  Color3.fromRGB(255,255,255),
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
                currentColor = c
                swatch.BackgroundColor3 = c
                pcall(callback, c)
            end)
        end

        local open = false
        local overlay = makeOverlay(f)
        applyHover(overlay, f)

        overlay.MouseButton1Click:Connect(function()
            open = not open
            if open then
                panel.Visible = true
                tween(panel, 0.16, { Size = UDim2.new(1, 0, 0, 40) })
            else
                tween(panel, 0.14, { Size = UDim2.new(1, 0, 0, 0) })
                task.delay(0.15, function() panel.Visible = false end)
            end
        end)

        return {
            SetColor = function(_, c) currentColor = c; swatch.BackgroundColor3 = c end,
            GetColor = function() return currentColor end,
        }
    end

    ----------------------------------------------------------------
    -- Visibility helpers
    -- NOTE: ToggleVisible (not Toggle) to avoid colliding with the
    --       Toggle element builder above.
    ----------------------------------------------------------------
    function window:Show()          main.Visible = true            end
    function window:Hide()          main.Visible = false           end
    function window:ToggleVisible() main.Visible = not main.Visible end

    function window:Destroy() main:Destroy() end

    table.insert(library.windows, window)
    return window
end

----------------------------------------------------------------------
-- Destroy everything
----------------------------------------------------------------------
function library:Destroy()
    if self.gui then
        self.gui:Destroy()
        self.gui = nil
    end
    self.windows     = {}
    self._notifQueue = {}
end

return library

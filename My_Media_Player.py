import tkinter as tk
from tkinter import *
from tkinter import ttk, font, filedialog, messagebox
import numpy as np
from pathlib import Path
import subprocess
from pynput import keyboard
from pynput.keyboard import Key, Controller
from threading import Timer
import time
from time import perf_counter_ns 
import pyaudio # Only Used To Retrieve Default Audio Output Device 
from pygame import mixer # Pygame Only Used To Retrieve All Audio Output Devices
import pygame._sdl2.audio as sdl2_audio
from ctypes import cast, POINTER
import cv2
import json
import random
from comtypes import CLSCTX_ALL
from pycaw.pycaw import AudioUtilities, IAudioEndpointVolume
import pywinctl as window
import win32gui
from win32api import GetMonitorInfo, MonitorFromPoint
import os
import sys
class FFPLAY():
    def __init__(self,parent):
        self.parent=parent
        self.Media_Widgets={}# Entry widgets For Destruction (Media File Names)
        self.Index_Widgets={}# Label widgets For Destruction (Media File Index)
        self.ffplay_window=None# ffplay Window
        self.process_ffplay=None# ffmplay Process
        self.ffplay_running=False# ffplay Process Status
        self.cv2_running=False# CV2 Image Status
        self.click_next=False# Media File Finished, Simulate Next Button Click
        self.next_ready=True
        self.timer=None# Timer Thread For Slider Clock
        self.timer_running=False# Timer Thread Status
        self.listener=None# Keyboard Listener
        self.Media_Dict={}# Shuffled Or UnShuffled Song,Video,Image Dictionary
        self.Original_Dict={}# Original Sorted Unshuffled
        self.active_database=""
        self.active_media=""
        self.active_file=""
        self.Index=[]# Index Widgets
        self.Media_Btn=[]# Media Widgets
        self.key_now=None# Active Media File Key
        self.last_key=None
        self.repeat=False
        self.shuffled=False
        self.seeking=False
        self._duration=0
        self._start_time=0.0
        self._interval=0.1
        self._time_now=0.0
        self._elapsed_time=0.0
        self._paused_time=0.0
        self._factor=1.0
        self._ns_time=0
        self.video_path=os.path.join(Path(__file__).parent.absolute(),"Videos.json")
        self.video_favorite_path=os.path.join(Path(__file__).parent.absolute(),"Videos_Favorite.json")
        self.video_karoake_path=os.path.join(Path(__file__).parent.absolute(),"Videos_Karoake.json")
        self.music_path=os.path.join(Path(__file__).parent.absolute(),"Music.json")
        self.music_favorite_path=os.path.join(Path(__file__).parent.absolute(),"Music_Favorite.json")
        self.image_path=os.path.join(Path(__file__).parent.absolute(),"Images.json")
        self.image_family_path=os.path.join(Path(__file__).parent.absolute(),"Images_family.json")
        self.image_favorite_path=os.path.join(Path(__file__).parent.absolute(),"Images_favorite.json")
        self.setup_path=os.path.join(Path(__file__).parent.absolute(),"Setup.json")
        self.ffmpeg_audio_exts=['mp3','wma','wav','mp2','ac3','aac','eac3','m4a','wmav1','wmav2','opus','ogg','aiff','alac','ape','flac']
        self.ffmpeg_video_exts=['mp4','avi','mov','mkv','mpg','mpeg','wmv','webm','flv','mj2','3gp','3g2']
        self.ffmpeg_image_exts=['bmp','jpg','jpeg','gif','png','ppm','dib']
    def get_duration(self,file):# minutes = "-sexagesimal", seconds = Blank
        try:
            proc=subprocess.Popen(["ffprobe","-i",file,"-show_entries","format=duration","-v","quiet","-of","csv=p=0"], 
                                    stdout=subprocess.PIPE,creationflags=subprocess.CREATE_NO_WINDOW, stderr=subprocess.PIPE)
            stdout,stderr=proc.communicate()
            proc.terminate()
            output=stdout.strip()# Capture the standard output as a string
            video_length=output.decode()[:-1]
            err=(stderr.decode()[:-1])
            if err!='' or video_length=='' or proc.returncode!=0:# Try Different Approach
                proc=subprocess.Popen(["ffprobe","-v","error","-select_streams","v:0","-show_entries","stream=duration","-of","default=noprint_wrappers=1:nokey=1",file], 
                                        stdout=subprocess.PIPE,creationflags=subprocess.CREATE_NO_WINDOW, stderr=subprocess.PIPE)
                stdout,stderr=proc.communicate()
                proc.terminate()
                output=stdout.strip()# Capture the standard output as a string
                video_length=output.decode()[:-1]
                err=(stderr.decode()[:-1])
                if err!='' or video_length=='' or proc.returncode!=0:raise Exception("ffprobe Get Stream Duration")# Try Different Approach
            video_length=round(float(video_length),3)
            return video_length
        except Exception as e:
            title='<FFPROBE Get Stream Duration>'
            msg1='Retrieving Stream Duration Failed!\n'
            msg2=f"Error: '{e}'"
            messagebox.showerror(title, msg1+msg2)
            self._stop()                
            return None
    def begin_seeking(self,event):
        clicked=time_scale.identify(event.x, event.y)
        if self.ffplay_running:
            if clicked=="trough1":
                self.send_keyboard_key("left")
                if self._time_now-10<0.0:self._time_now=0.0
                else:self._time_now-=10
            elif clicked=="trough2":
                self.send_keyboard_key("right")
                if self._time_now+10>self._duration:self._time_now=self._duration
                else: self._time_now+=10
            elif clicked=="slider": 
                self.pause(self)
                self.seeking=True
        elif self.cv2_running and int(Slide_Show_Delay.get())>0:
            if clicked=="slider": 
                self.pause(self)
                self.seeking=True
    def end_seeking(self,event):
        unclicked=time_scale.identify(event.x, event.y)
        if self.ffplay_running:
            if unclicked=="slider" or unclicked=="": 
                basename=os.path.basename(self.active_file)
                ext=str(os.path.splitext(basename)[1].replace(".",""))
                if ext.lower() in self.ffmpeg_image_exts:
                    time_scale.set(0.0)
                    self._start_time=time_scale.get()
                    return# Image File
                self._start_time=time_scale.get()
                self._time_now=float(time_scale.get())
                self.pause(self)
                self._stop(True)
                self.seeking=False
                if self.shuffled:
                    shuffle_btn.configure(background="#00ffff")
                    play_btn.configure(background="#bcbcbc")
                    stop_btn.configure(background="#bcbcbc",text="Stop")
                else:
                    play_btn.configure(background="#00ffff")
                    stop_btn.configure(text="Stop",background="#bcbcbc")
                    shuffle_btn.configure(background="#bcbcbc")
                root.update()
                self.next_ready=True
                if self.active_media=="music" or self.active_media=="video":self.play_av(self.active_file,self.key_now)
                elif self.active_media=="image":self.play_images(self.active_file,self.key_now)
        elif self.cv2_running and int(Slide_Show_Delay.get())>0:
            if unclicked=="slider" or unclicked=="": 
                pos=time_scale.get()
                self._start_time=pos
                self._time_now=float(pos)
                self.pause(self)
                self.seeking=False
        elif self.cv2_running and int(Slide_Show_Delay.get())==0:
            time_scale.set(0.0)
            time_scale.update()
    def on_release(self,key):
        if key.char=="s":#Stop Slide Show
            self.listener.stop()
            root.update()
            self._stop()
            return False
        elif key.char=="q":# Exit Program       
            self.listener.stop()
            root.update()
            self.stop_process()
            destroy()
    def set_window_coord(self,wid,hgt):
        if Screen_Position.get()=="Top Left":
            _x,_y=0,0
        elif Screen_Position.get()=="Top Center":
            _x,_y=int((work_area[2]/2)-(int(wid)/2)),0
        elif Screen_Position.get()=="Top Right":
            _x,_y=work_area[2]-int(wid),0
        elif Screen_Position.get()=="Center Left":
            _x,_y=0,int((work_area[3]/2)-(int(hgt)/2))
        elif Screen_Position.get()=="Center":
            _x,_y=int((work_area[2]/2)-(int(wid)/2)),int((work_area[3]/2)-(int(hgt)/2))
        elif Screen_Position.get()=="Center Right":
            _x,_y=int((work_area[2])-(int(wid))),int((work_area[3]/2)-(int(hgt)/2))
        elif Screen_Position.get()=="Bottom Left":
            _x,_y=0,work_area[3]-(int(hgt))
        elif Screen_Position.get()=="Bottom Center":
            _x,_y=int((work_area[2]/2)-(int(wid)/2)),work_area[3]-(int(hgt))
        elif Screen_Position.get()=="Bottom Right":
            _x,_y=int((work_area[2])-(int(wid))),work_area[3]-(int(hgt))
        return _x,_y    
    def play_images(self,file,key):# Images/Photos etc...
        if self.next_ready:
            self.key_now=key
            self.next_ready=False
            if not self.cv2_running:self.remove_menubar()
            self.active_file=file
            if not self.cv2_running:# Not Running
                self.remove_menubar()
                self.click_next=False
                stop_btn.configure(text="Stop",background="#bcbcbc")
                self.Media_Btn[key].configure(fg="#4cffff")
                self.Media_Btn[key].update()
                self._reset_timer()
            self.listener=keyboard.Listener(on_release=self.on_release)
            self.listener.start()
            time.sleep(0.1)
            if int(Slide_Show_Delay.get())==0:self.load_image_menu()
            elif int(Slide_Show_Delay.get())>0:self.update_time_scale(float(Slide_Show_Delay.get())) 
            while self.listener.running:
                try:
                    stop_btn.configure(text="Stop",background="#bcbcbc")
                    title_lbl.configure(text=f"Showing Image File: {os.path.basename(self.Media_Dict[str(self.key_now)])}")
                    self.Media_Btn[self.key_now].configure(fg="#4cffff")
                    self.Media_Btn[self.key_now].update()
                    cv2.destroyAllWindows()
                    img=cv2.imread(file,cv2.IMREAD_UNCHANGED)
                    self.active_file=file
                    window_hgt=Screen_Height.get()
                    hgt, wid=img.shape[:2]
                    img_aspect_ratio=wid/hgt
                    if hgt>window_hgt:hgt=window_hgt
                    scale_factor=int(window_hgt)/hgt  # Percent of original size
                    window_hgt=int(hgt * scale_factor)
                    if window_hgt<hgt:window_hgt=hgt
                    window_wid=int(window_hgt * img_aspect_ratio)
                except Exception:
                    self.remove_media_file()# Remove corrupted Image File From Library
                    continue
                if window_wid>work_area[2]:window_wid=work_area[2]
                if window_hgt>work_area[3]:window_hgt=work_area[3]
                window_x,window_y=self.set_window_coord(window_wid,window_hgt)
                try:
                    window_title=f"My Media Player: Playing {file}"
                    if self.key_now==0:self.parent.canvas.yview_moveto((1/len(self.Media_Dict))*self.key_now)
                    else:self.parent.canvas.yview_moveto((1/len(self.Media_Dict))*(self.key_now-1))# @ 2 down to show previous song
                    self.parent.canvas.update()
                    if self.active_media=="image":
                        try:
                            dim=(window_wid, window_hgt)
                            resized_img=cv2.resize(img,dim,interpolation=cv2.INTER_AREA)
                            cv2.setWindowTitle("My Media Player", window_title)
                            cv2.imshow("My Media Player", resized_img)
                            self.ffplay_window=window.getWindowsWithTitle(window_title)[0]# Window
                            handle=win32gui.FindWindow(None, window_title)# Window Handle
                            win32gui.MoveWindow(handle, window_x, window_y, window_wid, window_hgt, 1)
                            cv2.waitKey(1)
                            self.cv2_running=True
                            self.next_ready=True
                            self.ffplay_running=False
                            Start_Time.set(perf_counter_ns())
                            self._time_now=0
                            self._factor=1
                            self.last_key=self.key_now
                            self.ffplay_window.activate()
                            if int(Slide_Show_Delay.get())==0:time_delay=300# 5 Minutes If Slide_Show_Delay=0
                            elif int(Slide_Show_Delay.get())>0:time_delay=int(Slide_Show_Delay.get()) 
                            if time_delay>0:# Time Loop For Catching Button Press's Stop Or Quit 
                                while self._time_now<time_delay and self.listener.running:
                                    time.sleep(0.1)
                                    if Paused.get()==True:# self._factor Is Correction For Paused Time For Slider
                                        self._paused_time=perf_counter_ns()
                                        self._factor=self._ns_time/self._paused_time
                                        root.update()
                                    else:
                                        self._ns_time=perf_counter_ns()*self._factor
                                        self._elapsed_time=(self._ns_time-Start_Time.get())/1000000000
                                        self._time_now+=self._elapsed_time
                                        if time_delay<=120:time_scale.set(self._time_now)
                                        Start_Time.set(Start_Time.get()+(self._elapsed_time*1000000000))
                                        root.update()
                                        if self.key_now!=self.last_key:break
                                if self.key_now!=self.last_key and self.key_now!=None:
                                    self.Media_Btn[self.last_key].configure(fg="#ffffff")
                                    self.Media_Btn[self.last_key].update()    
                                    if not self.repeat:
                                        file=self.Media_Dict[str(self.key_now)]
                                    else:
                                        self.key_now=self.last_key
                                        file=self.Media_Dict[str(self.last_key)]        
                                elif self.key_now!=None:
                                    self.Media_Btn[self.key_now].configure(fg="#ffffff")
                                    self.Media_Btn[self.key_now].update()    
                                    if not self.repeat:
                                        if self.key_now==len(self.Media_Dict)-1:
                                            file=self.Media_Dict["0"]
                                            self.key_now=0
                                        else:    
                                            self.key_now+=1
                                            file=self.Media_Dict[str(self.key_now)]
                                    else:file=self.Media_Dict[str(self.key_now)]        
                                root.update()        
                            else:self.listener.stop()            
                        except Exception as e:
                            self.remove_media_file()# Remove corrupted Image File From Libraryqq
                            continue
                except Exception as e:
                    title='<CV2 Slide Show>'
                    msg1='Slide Show Failed!\n'
                    msg2=f"Error: '{e}'"
                    msg=msg1+msg2
                    messagebox.showerror(title, msg)
                    self._stop()
    def play_av(self,file,key):# Audio/Video Files
        if self.next_ready:
            self.key_now=key
            self.next_ready=False
            self.active_file=file
            if not self.ffplay_running:# Not Running
                self.remove_menubar()
                self.click_next=False
                stop_btn.configure(text="Stop",background="#bcbcbc")
                self.Media_Btn[key].configure(fg="#4cffff")
                self.Media_Btn[key].update()
                self._reset_timer()
                title_lbl.configure(text=f"Audio Playing On {self.Active_Device}, {os.path.basename(self.Media_Dict[str(self.key_now)])}")
                self._duration=self.get_duration(file)# Duration In Seconds
                if self._duration==None:return
                self.update_time_scale(self._duration)
                window_hgt=str(Screen_Height.get())
                window_wid=str(int(Screen_Height.get()*aspect_ratio))   
                if int(window_wid)>work_area[2]:window_wid=str(work_area[2])
                if int(window_hgt)>work_area[3]:window_hgt=str(work_area[3])
                window_x,window_y=self.set_window_coord(window_wid,window_hgt)
                try:
                    window_title=f"My Media Player: Playing {file}"
                    if key==0:self.parent.canvas.yview_moveto((1/len(self.Media_Dict))*key)
                    else:self.parent.canvas.yview_moveto((1/len(self.Media_Dict))*(key-1))# @ 2 down to show previous song
                    self.parent.canvas.update()
                    self.process_ffplay=subprocess.Popen(["ffplay","-ss",str(self._start_time),"-t",str(self._duration),"-x",window_wid,"-y", window_hgt,"-autoexit",file,"-window_title", window_title],
                                                        stdin=subprocess.PIPE,stdout=subprocess.PIPE,creationflags=subprocess.CREATE_NO_WINDOW)
                    poll=""
                    count=0# Exit Backup
                    while poll!=None and count<=20:# 20 = 2 Seconds Max Time For Loop
                        count+=1
                        try:
                            time.sleep(0.1)
                            poll=self.process_ffplay.poll()
                        except Exception:
                            pass
                    if count>=20:
                        self.remove_media_file()# Remove corrupted Video File From Library
                        return
                    if poll==None:# None = ffplay Running
                        Start_Time.set(perf_counter_ns())
                        self.ffplay_running=True
                        self.cv2_running=False
                        ready=False
                        count=0# Exit Backup
                        while ready==False and count<=20:# 20 = 2 Seconds Max Time For Loop
                            count+=1
                            try:
                                time.sleep(0.1)
                                self.ffplay_window=window.getWindowsWithTitle(window_title)[0]# Window
                                if self.ffplay_window is not None:ready=True
                            except Exception as e:
                                pass
                        if count>=20:raise Exception("getWindowsWithTitle()")# Allow 2 Seconds        
                        handle=win32gui.FindWindow(None, window_title)# Window Handle
                        win32gui.MoveWindow(handle, window_x, window_y, int(window_wid), int(window_hgt), 1)
                        self.ffplay_window.activate()
                        if not self.timer_running:
                            self._start_timer_thread()
                    else:raise Exception("ffplay Not Running")
                except Exception as e:
                    title='<FFPLAY Starting Stream>'
                    msg1='Starting Stream Failed!\n'
                    msg2=f"Error: '{e}'"
                    msg=msg1+msg2
                    messagebox.showerror(title, msg)
                    self._stop()
    def _start_timer_thread(self):
        self.next_ready=True
        if self.click_next==True:
            next=lambda:self.ctrl_btn_clicked(self,"next")
            next()
        else:
            self.timer=Timer(self._interval, self._update_timer)
            self.timer_running=True
            self.timer.start()
    def _update_timer(self):
        if self.timer_running==False or self.ffplay_running==False and self.cv2_running==False:return 
        if Paused.get()==True:# self._factor Is Correction For Paused Time For Slider
            self._paused_time=perf_counter_ns()
            self._factor=self._ns_time/self._paused_time
        else:
            self._ns_time=perf_counter_ns()*self._factor
            self._elapsed_time=(self._ns_time-Start_Time.get())/1000000000
            self._time_now+=self._elapsed_time
            time_scale.set(self._time_now)
            Start_Time.set(Start_Time.get()+(self._elapsed_time*1000000000))
            if self.ffplay_running:
                poll=self.process_ffplay.poll()
                if poll!=None:self.click_next=True# ffplay not running, Terminated By -autoexit, Ready Next File
        level=self.Master_Volume.GetMasterVolumeLevelScalar()# Volume Slider Level / 100
        Level.set(level*100)# Track Volume From Other Sliders (Windows, Sound Card)
        self._start_timer_thread()
    def _reset_timer(self):        
        Start_Time.set(0.0)
        time_scale.set(self._start_time)
        time_scale.update()
        self._interval=0.1
        self.timer_running=False
        self._time_now=self._start_time
        self._elapsed_time=0.0
        self._paused_time=0.0
        self._factor=1.0
        self._ns_time=0
    def stop_process(self):# Used For Advancing Media Files
            if self.timer_running:
                self.timer.cancel()
                self.timer_running=False
            try:    
                if self.ffplay_running:
                    poll=self.process_ffplay.poll()
                    while poll==None:
                        self.send_keyboard_key("quit")
                        poll=self.process_ffplay.poll()
                    self.process_ffplay.terminate()
                    self.process_ffplay.kill()
                    self.ffplay_running=False
                if self.key_now!=None:
                    self.last_key=self.key_now
                    self.Media_Btn[self.last_key].configure(fg="#ffffff")
                    self.Media_Btn[self.last_key].update()
            except Exception:pass
            root.focus_force()
    def _stop(self,skip_menu=None):# Used For Stopping Media File
        if self.cv2_running:
            cv2.destroyAllWindows() 
            self.remove_menubar()
            root.update()
            self.cv2_running=False    
        if self.ffplay_running or self.cv2_running:self.stop_process()
        if not self.seeking:
            title_lbl.configure(text="")
            time_scale.set(0.0)
            self.update_time_scale(0.0)    
            self.last_key=self.key_now
            play_btn.configure(background="#bcbcbc")
            shuffle_btn.configure(background="#bcbcbc")
            stop_btn.configure(text="Stopped",background="#00ffff",)
            pause_btn.configure(text="Pause",background="#bcbcbc")# Pausekey
            Paused.set(False)
            self.Master_Volume.SetMute(False, None)
            mute_btn.config(text="Mute",background="#bcbcbc")
            if skip_menu==None :self.load_menubar()
            if self.key_now==None:return
            self.Media_Btn[self.key_now].configure(bg="#001829",fg="#ffffff")
            self.Media_Btn[self.key_now].update()
            self.key_now=None
            self.last_key=None
            self.parent.canvas.yview_moveto(0)
            root.update()
    def update_time_scale(self,sec):
        sec=float(sec)
        if sec>=20:sec=int(round((sec),3))+1
        mods={8:sec%8,9:sec%9,10:sec%10,11:sec%11,12:sec%12,13:sec%13,14:sec%14,15:sec%15,16:sec%16,17:sec%17,18:sec%18,}
        interval=round(sec/min(mods,key=mods.get),2)# Set Lowest Modulo For Intervals
        time_scale.config(from_=0.0,to=sec)
        time_scale.config(tickinterval=(interval))
        time_scale.config(resolution=0.01)
    def remove_menubar(self):
        try:
            self.menubar.delete(0, END)
            empty_menu=Menu(root)
            root.config(menu=empty_menu)
            root.update()
        except Exception:pass
    def send_keyboard_key(self,key):
        keyboard=Controller()
        mykeys=[Key.left,Key.right,Key.up,Key.down,"p","q","s"]
        if self.ffplay_running:
            self.ffplay_window.activate()
            if key=="left":key_now=mykeys[0]
            elif key=="right":key_now=mykeys[1]
            elif key=="up":key_now=mykeys[2]
            elif key=="down":key_now=mykeys[3]
            elif key=="pause":key_now=mykeys[4]
            elif key=="quit":key_now=mykeys[5]
            keyboard.press(key_now)
            time.sleep(0.1)
            keyboard.release(key_now)
        elif self.cv2_running:   
            if key=="quit":
                key_now=mykeys[5]
            elif key=="stop":
                key_now=mykeys[6]
            keyboard.press(key_now)
            time.sleep(0.1)
            keyboard.release(key_now)
        if key=="quit":
            key_now=mykeys[5]
            keyboard.press(key_now)
            time.sleep(0.1)
            keyboard.release(key_now)
    def slider_released(self):
        try:
            if self.ffplay_running:self.ffplay_window.activate()
        except Exception:pass
    def set_master_volume(self):
        self.Master_Volume.SetMasterVolumeLevelScalar(Level.get()/100, None)
        level=self.Master_Volume.GetMasterVolumeLevelScalar()# Volume Slider Level / 100
        if level==0:self.Master_Volume.SetMute(True, None)
        else:self.Master_Volume.SetMute(False, None)
    def ctrl_btn_clicked(self,event,btn):
        if self.Media_Dict:
            if btn=="btn play":
                if self.shuffled:
                    if Paused.get():self.pause(self)
                    if self.ffplay_running:self.stop_process()
                    if self.cv2_running:self.listener.stop()
                    self.shuffled=False
                    self.load_library(self.active_database)
                else:
                    if self.ffplay_running or self.cv2_running:return# If Playing, Do Nothing
                self._start_time=0.0
                play_btn.configure(background="#00ffff")
                stop_btn.configure(text="Stop",background="#bcbcbc")
                shuffle_btn.configure(background="#bcbcbc")
                root.update()
                file=self.Media_Dict["0"]
                self.key_now=0
                if self.active_media=="music" or self.active_media=="video":self.play_av(file,self.key_now)
                elif self.active_media=="image":self.play_images(file,self.key_now)
            elif btn=="media play":# File Clicked In Window
                if Paused.get():self.pause(self)
                if self.ffplay_running:self.stop_process()
                if not self.shuffled:
                    play_btn.configure(background="#00ffff")
                    stop_btn.configure(text="Stop",background="#bcbcbc")
                else:    
                    shuffle_btn.configure(background="#00ffff")
                    play_btn.configure(background="#bcbcbc")
                root.update()
                self._start_time=0.0
                file=self.Media_Dict[event.widget._name]
                self.key_now=int(event.widget._name)
                if self.active_media=="music" or self.active_media=="video":self.play_av(file,self.key_now)
                elif self.active_media=="image":
                    if not self.cv2_running:self.play_images(file,self.key_now)
            elif btn=="shuffled":
                if Paused.get():self.pause(self)
                if self.ffplay_running:self.stop_process()
                if self.cv2_running:self.listener.stop()
                self.shuffled=True
                self.load_library(self.active_database)
                self._start_time=0.0
                shuffle_btn.configure(background="#00ffff")
                play_btn.configure(background="#bcbcbc")
                stop_btn.configure(background="#bcbcbc",text="Stop")
                root.update()
                file=self.Media_Dict["0"]
                self.key_now=0
                if self.active_media=="music" or self.active_media=="video":self.play_av(file,self.key_now)
                elif self.active_media=="image":self.play_images(file,self.key_now)
            elif btn=="next":
                if Paused.get():self.pause(self)
                if self.next_ready:# Prevent Multiple Windows
                    self._start_time=0.0
                    if self.ffplay_running:self.stop_process()
                    if self.last_key!=None:
                        if self.repeat:
                            self.key_now=self.last_key   
                            file=self.Media_Dict[str(self.key_now)]
                        elif self.last_key==len(self.Media_Dict)-1:
                            file=self.Media_Dict["0"]
                            self.key_now=0
                        else:    
                            self.key_now=self.last_key+1    
                            file=self.Media_Dict[str(self.key_now)]
                    else:
                        play_btn.configure(background="#00ffff")
                        stop_btn.configure(text="Stop",background="#bcbcbc")
                        root.update()
                        file=self.Media_Dict["0"]
                        self.key_now=0
                    if self.active_media=="image":
                        if not self.cv2_running:self.play_images(file,self.key_now)
                    elif self.active_media=="music" or self.active_media=="video":self.play_av(file,self.key_now)
            elif btn=="previous":
                if Paused.get():self.pause(self)
                if self.next_ready:# Prevent Multiple Windows
                    self._start_time=0.0
                    self.click_next=False
                    if self.ffplay_running:self.stop_process()
                    if self.last_key!=None:
                        if self.repeat:
                            self.key_now=self.last_key   
                            file=self.Media_Dict[str(self.key_now)]
                        elif self.last_key!=0:
                            self.key_now=self.last_key-1    
                            file=self.Media_Dict[str(self.key_now)]
                        else:# self.last_key=0
                            self.key_now=len(self.Media_Dict)-1
                            file=self.Media_Dict[str(self.key_now)]
                    else:
                        play_btn.configure(background="#00ffff")
                        stop_btn.configure(text="Stop",background="#bcbcbc")
                        root.update()
                        file=self.Media_Dict["0"]
                        self.key_now=0
                    if self.active_media=="image":
                        if not self.cv2_running:self.play_images(file,self.key_now)
                    elif self.active_media=="music" or self.active_media=="video":self.play_av(file,self.key_now)
            elif btn=="repeat":
                if self.cv2_running and int(Slide_Show_Delay.get())==0:return
                self._start_time=0.0
                if self.repeat==False:
                    self.repeat=True
                    repeat_btn.configure(background="#00ffff")
                    repeat_btn.update()
                else:
                    self.repeat=False   
                    repeat_btn.configure(background="#bcbcbc")
                    repeat_btn.update()
            elif btn=="stop":
                if self.ffplay_running or self.cv2_running:
                    if self.cv2_running:self.send_keyboard_key("stop")
                    self._stop()
            elif btn=="mute":
                if self.ffplay_running:
                    txt=mute_btn.cget("text")
                    if txt=="Mute":
                        self.Master_Volume.SetMute(True, None)
                        mute_btn.config(text="UnMute",background="#00ffff")
                    elif txt=="UnMute":# Unmute Clicked
                        self.Master_Volume.SetMute(False, None)
                        mute_btn.config(text="Mute",background="#bcbcbc")
    def pause(self,event):
        if self.ffplay_running:
            self.ffplay_window.activate()
            self.send_keyboard_key("pause")
            if pause_btn.cget("text")=="Pause":
                Paused.set(True)
                pause_btn.configure(text="Unpause",background="#00ffff")# Resume
            elif pause_btn.cget("text")=="Unpause":# Resume Clicked
                Paused.set(False)
                pause_btn.configure(text="Pause",background="#bcbcbc")# Pause
        elif self.cv2_running and int(Slide_Show_Delay.get())>0:
            if pause_btn.cget("text")=="Pause":
                Paused.set(True)
                pause_btn.configure(text="Unpause",background="#00ffff")# Resume
            elif pause_btn.cget("text")=="Unpause":# Resume Clicked
                Paused.set(False)
                pause_btn.configure(text="Pause",background="#bcbcbc")# Pause
    def quit(self,event):
        self.stop_process()
        destroy()
    def rotate_image(self):
        title="<Image Rotation>"
        msg1="Enter Image Rotation In Degrees.\n"
        msg2="Range Is From -360 To 360 Degrees!\n"
        msg3="A Negative Number Rotates The Image Clock-Wise.\n"
        msg4="A Positive Number Rotates The Image Counter Clock-Wise."
        msg=msg1+msg2+msg3+msg4
        angle=my_askinteger(title,msg,180,-360,360)
        if angle!=None:
            try:
                img=cv2.imread(self.active_file,cv2.IMREAD_UNCHANGED)
                h, w = img.shape[:2]
                center = (w // 2, h // 2)
                abs_cos, abs_sin = abs(np.cos(np.radians(angle))), abs(np.sin(np.radians(angle)))
                bound_w = int(h * abs_sin + w * abs_cos)
                bound_h = int(h * abs_cos + w * abs_sin)
                rotation_matrix = cv2.getRotationMatrix2D(center, angle, 1.0)
                rotation_matrix[0, 2] += bound_w / 2 - center[0]
                rotation_matrix[1, 2] += bound_h / 2 - center[1]
                rotated_img = cv2.warpAffine(img, rotation_matrix, (bound_w, bound_h))
                cv2.imwrite(self.active_file, rotated_img)
                if self.active_media=="image":self.play_images(self.active_file,self.key_now)
            except Exception as e:
                title='<Image Rotation>'
                msg1='Rotating Image Failed!\n'
                msg2='This File May Be Corrupted!\n'
                msg2=f"Error: '{e}'"
                messagebox.showerror(title, msg1+msg2)
    def remove_media_file(self):
        if self.active_database=="Images":db_path=self.image_path
        elif self.active_database=="Images_Family":db_path=self.image_family_path
        elif self.active_database=="Images_Favorite":db_path=self.image_favorite_path
        elif self.active_database=="Music":db_path=self.music_path
        elif self.active_database=="Music_Favorite":db_path=self.music_favorite_path
        elif self.active_database=="Videos":db_path=self.video_path
        elif self.active_database=="Videos_Favorite":db_path=self.video_favorite_path
        elif self.active_database=="Videos_Karoake":db_path=self.video_karoake_path
        if os.path.isfile(self.active_file):
            next_key=str(self.key_now)
            del self.Media_Dict[next_key]
            temp_dict=self.Media_Dict.copy()
            self.Media_Dict.clear()
            count=0
            temp_dict2={}
            for key, value in temp_dict.items():
                temp_dict2[str(count)]=value
                count+=1
            self.clear_database(self.active_database)
            with open(db_path, "w") as outfile:json.dump(temp_dict2, outfile)
            outfile.close()
            self.load_library(self.active_database,True)
            if len(self.Media_Dict)>=1:
                if int(next_key)==len(self.Media_Dict):next_key="0"
                self.active_file=self.Media_Dict.get(next_key)
                self.key_now=int(next_key)
                self.next_ready=True
                temp_dict.clear()
                temp_dict2.clear()
                self.active_file,self.key_now
                if self.active_media=="music" or self.active_media=="video":self.play_av(self.active_file,self.key_now)
                elif self.active_media=="image":self.play_images(self.active_file,self.key_now)
    def load_image_menu(self):
        self.menubar=Menu(root,fg="#000000")# Create Menubar
        images_menu=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)# File Menu and commands
        self.menubar.add_cascade(label=' Images ',menu=images_menu)
        images_menu.add_command(label='Rotate Image And Save',command=lambda:self.rotate_image())
        images_menu.add_separator()
        images_menu.add_command(label='Delete Image',command=lambda:self.remove_media_file())
        root.config(menu=self.menubar)
        root.update()
    def load_menubar(self):
        self.menubar=Menu(root,fg="#000000")# Create Menubar
        music_menu=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        self.menubar.add_cascade(label='  Media Libraries ',menu=music_menu)
        upload_music=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        upload_music.add_command(label="Load Music Library",command=lambda:self.load_library("Music"))
        upload_music.add_separator()
        upload_music.add_command(label="Upload Music Folder To Library",command=lambda:self.find_in_folder("Music"))
        upload_music.add_separator()
        upload_music.add_command(label="Upload Music File/s To Library",command=lambda:self.add_files_to_db("Music"))
        upload_music.add_separator()
        upload_music.add_command(label="Remove Music Files From Library",command=lambda:self.clear_database("Music"))
        music_menu.add_cascade(label='Music Library',menu=upload_music)
        favorite_music=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        favorite_music.add_command(label="Load Favorites Music Library",command=lambda:self.load_library("Music_Favorite"))
        favorite_music.add_separator()
        favorite_music.add_command(label="Upload Favorite Music Folder To Library",command=lambda:self.find_in_folder("Music_Favorite"))
        favorite_music.add_separator()
        favorite_music.add_command(label="Upload Favorites Music File/s To Library",command=lambda:self.add_files_to_db("Music_Favorite"))
        favorite_music.add_separator()
        favorite_music.add_command(label="Remove Favorites Music Files From Library",command=lambda:self.clear_database("Music_Favorite"))
        music_menu.add_cascade(label="Favorites Music Library",menu=favorite_music)
        music_menu.add_separator()
        upload_videos=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        upload_videos.add_command(label="Load Video Library",command=lambda:self.load_library("Videos"))
        upload_videos.add_separator()
        upload_videos.add_command(label="Upload Video Folder To Library",command=lambda:self.find_in_folder("Videos"))
        upload_videos.add_separator()
        upload_videos.add_command(label="Upload Video File/s To Library",command=lambda:self.add_files_to_db("Videos"))
        upload_videos.add_separator()
        upload_videos.add_command(label="Remove Video Files From Library",command=lambda:self.clear_database("Videos"))
        music_menu.add_cascade(label='Video Library',menu=upload_videos)
        favorite_videos=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        favorite_videos.add_command(label="Load Favorites Video Library",command=lambda:self.load_library("Videos_Favorite"))
        favorite_videos.add_separator()
        favorite_videos.add_command(label="Upload Favorite Video Folder To Library",command=lambda:self.find_in_folder("Videos_Favorite"))
        favorite_videos.add_separator()
        favorite_videos.add_command(label="Upload Favorites Video File/s To Library",command=lambda:self.add_files_to_db("Videos_Favorite"))
        favorite_videos.add_separator()
        favorite_videos.add_command(label="Remove Favorites Video Files From Library",command=lambda:self.clear_database("Videos_Favorite"))
        music_menu.add_cascade(label='Favorites Video Library',menu=favorite_videos)
        karoake_videos=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        karoake_videos.add_command(label="Load Karoake Video Library",command=lambda:self.load_library("Videos_Karoake"))
        karoake_videos.add_separator()
        karoake_videos.add_command(label="Upload Karoke Video Folder To Library",command=lambda:self.find_in_folder("Videos_Karoake"))
        karoake_videos.add_separator()
        karoake_videos.add_command(label="Upload Karoake Video File/s To Library",command=lambda:self.add_files_to_db("Videos_Karoake"))
        karoake_videos.add_separator()
        karoake_videos.add_command(label="Remove Karoake Video Files From Library",command=lambda:self.clear_database("Videos_Karoake"))
        music_menu.add_cascade(label='Karoake Video Library',menu=karoake_videos)
        music_menu.add_separator()
        upload_image=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        upload_image.add_command(label="Load Image Library",command=lambda:self.load_library("Images"))
        upload_image.add_separator()
        upload_image.add_command(label="Upload Image Folder To Library",command=lambda:self.find_in_folder("Images"))
        upload_image.add_separator()
        upload_image.add_command(label="Upload Image File/s To Library",command=lambda:self.add_files_to_db("Images"))
        upload_image.add_separator()
        upload_image.add_command(label="Remove Image Files From Library",command=lambda:self.clear_database("Images"))
        music_menu.add_cascade(label='Image Library',menu=upload_image)
        family_image=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        family_image.add_command(label="Load Family Image Library",command=lambda:self.load_library("Images_Family"))
        family_image.add_separator()
        family_image.add_command(label="Upload Family Image Folder To Library",command=lambda:self.find_in_folder("Images_Family"))
        family_image.add_separator()
        family_image.add_command(label="Upload Family Image File/s To Library",command=lambda:self.add_files_to_db("Images_Family"))
        family_image.add_separator()
        family_image.add_command(label="Remove Family Image Files From Library",command=lambda:self.clear_database("Images_Family"))
        music_menu.add_cascade(label='Family Image Library',menu=family_image)
        favorite_image=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        favorite_image.add_command(label="Load Favorites Image Library",command=lambda:self.load_library("Images_Favorite"))
        favorite_image.add_separator()
        favorite_image.add_command(label="Upload Favorites Image Folder To Library",command=lambda:self.find_in_folder("Images_Favorite"))
        favorite_image.add_separator()
        favorite_image.add_command(label="Upload Favorites Image File/s To Library",command=lambda:self.add_files_to_db("Images_Favorite"))
        favorite_image.add_separator()
        favorite_image.add_command(label="Remove Favorites Image Files From Library",command=lambda:self.clear_database("Images_Favorite"))
        music_menu.add_cascade(label='Favorites Image Library',menu=favorite_image)
        music_menu.add_command(label="Image Slide Show",command=lambda:set_slide_show())
        screen_menu=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)#
        self.menubar.add_cascade(label=' Media Screen ',menu=screen_menu)
        screen_menu.add_command(label='Screen Size',command=lambda:set_screen_size())
        screen_menu.add_separator()
        screen_menu.add_command(label='Startup Position',command=lambda:set_screen_position())
        if os.path.isfile(soundview_path):
            devices=self.get_devices()
            device_menu=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
            self.menubar.add_cascade(label=' Select Audio Output Device ',menu=device_menu)
            for d in range(len(devices)):
                device_menu.add_command(label=devices[d],command=lambda x=devices[d]:self.select_output_device(x))
                device_menu.add_separator()
            svv=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
            svv.add_command(label="View / Configure All Devices",command=lambda:open_soundview())
            device_menu.add_cascade(label='SoundVolumeView',menu=svv)
        about_menu=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
        self.menubar.add_cascade(label=' About ',menu=about_menu)
        about_menu.add_command(label='About My Media Player',command=lambda:about())
        root.config(menu=self.menubar)
        root.update()
    def initialize(self):
        try:
            default_device=pyaudio.PyAudio().get_default_output_device_info()["name"]
            devices=self.get_devices()
            pyaudio.PyAudio().terminate()
            result=list(filter(lambda x: default_device in x, devices))
            self.Active_Device=result[0]
            if self.Active_Device=="":
                self.Active_Device="Default"
            if os.path.isfile(soundview_path):    
                soundview_device=self.Active_Device.split("(", 1)[0].replace(" ","")
                cmd=[soundview_path, "/SetDefault", soundview_device, "1", "/Unmute", soundview_device, "/SetVolume", soundview_device, str(Level.get())]
                subprocess.run(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            devices=AudioUtilities.GetSpeakers()# Initialize Master Volumn Slider
            interface=devices.Activate(IAudioEndpointVolume._iid_, CLSCTX_ALL, None)
            self.Master_Volume=cast(interface, POINTER(IAudioEndpointVolume))
            Level.set(5)
            self.Master_Volume.SetMasterVolumeLevelScalar(Level.get()/100, None)
            Paused.set(False)
        except Exception as ex:
            title='<Interface Initialization>'
            msg1='Initialization Failed. Ending Program!\n'
            msg2=f"Error: '{ex}'"
            messagebox.showerror(title, msg1+msg2)
            destroy(None)
    def clear_database(self,db):
        if db=="Music":path=self.music_path
        elif db=="Music_Favorite":path=self.music_favorite_path
        elif db=="Videos":path=self.video_path
        elif db=="Videos_Favorite":path=self.video_favorite_path
        elif db=="Videos_Karoake":path=self.video_karoake_path
        elif db=="Images":path=self.image_path
        elif db=="Images_Family":path=self.image_family_path
        elif db=="Images_Favorite":path=self.image_favorite_path
        media=json.load(open(path, "r"))
        media.clear()
        json.dump(media,open(path, "w"),indent=4)
        if self.active_database==db:self.destroy_widgets()
    def check_duplicates(self,dict,searchFor):
        for value in dict.values():
            dict_path=Path(value)
            dict_value= os.path.basename(dict_path)
            search_path=Path(searchFor)
            search_value=os.path.basename(search_path)
            if search_value==dict_value:
                return True
        return False
    def add_files_to_db(self,db,files=None):
        music_exts=['*.mp3','*.wma','*.wav','*.mp2','*.ac3','*.aac','*.eac3','*.m4a',
                    '*.wmav1','*.wmav2','*.opus','*.ogg','*.aiff','*.alac','*.ape','*.flac']
        video_exts=['*.mp4','*.avi','*.mov','*.mkv','*.mpg','*.mpeg','*.wmv','*.webm','*.flv','*.mj2','*.3gp','*.3g2']
        image_exts=['*.bmp','*.jpg','*.jpeg','*.gif','*.png','*.ppm','*.dib']    
        if db=='Music':
            db_path=self.music_path
            exts=music_exts
            music=True
        elif db=='Music_Favorite':
            db_path=self.music_favorite_path
            exts=music_exts
            music=True
        elif db=='Videos':
            db_path=self.video_path    
            exts=video_exts
            music=False
        elif db=='Videos_Favorites':
            db_path=self.video_favorite_path  
            exts=video_exts
            music=False
        elif db=='Videos_Karoake':
            db_path=self.video_karoake_path   
            exts=video_exts
            music=False
        elif db=='Images':
            db_path=self.image_path    
            exts=image_exts
            music=False
        elif db=='Images_Family':
            db_path=self.image_family_path   
            exts=image_exts
            music=False
        elif db=='Images_Favorite':
            db_path=self.image_favorite_path
            exts=image_exts
            music=False
        if music==False:self.rename_msg()    
        if files==None:
            files=filedialog.askopenfilenames(title=f"Please Select Files To Upload To {db} Database.", filetypes=(("Media files", exts),))
            if files=="" or files==None:return
        else:files=[files]
        temp_dict=json.load(open(db_path, "r+"))
        count=len(temp_dict)
        if count>1200:return
        for _, name in enumerate(files):
            try:
                file_ext=os.path.splitext(name)[1].replace(".","*.")
                if file_ext.lower() in exts:
                    if music==False:# If Not Music File, Rename Files
                        file_path=self.rename_to_creation_date(name,db)
                        if file_path==None:continue
                    elif music==True:# If Music File, Check For Duplicates
                        file_path=name
                        if len(temp_dict)>=1:
                            if music==True:
                                exist=self.check_duplicates(temp_dict, file_path)
                                if exist:continue
                    temp_dict[count]=file_path
                    count+=1
                    if count>=1200:
                        msg1=f"Maximum Number Of 1200 {db} Has Been Reached.\n"
                        msg2="To Add More Files Please Select A Different Library!"
                        msg=msg1+msg2
                        messagebox.showinfo(f"<{db} Add To Library>",msg)
                        break
            except Exception:continue
        with open(db_path, "w") as outfile:json.dump(temp_dict, outfile)
        outfile.close()
        temp_dict.clear()
        if self.active_database==db:self.load_library(db)
    def rename_to_creation_date(self,path,db):
        if db=='Videos':prefix="VIDEO_"
        elif db=='Videos_Favorites':prefix="VIDEO_"
        elif db=='Videos_Karoake':prefix="VIDEO_"
        elif db=='Images':prefix="IMAGE_"
        elif db=='Images_Family':prefix="IMAGE_"
        elif db=='Images_Favorite':prefix="IMAGE_"
        else:return None
        try:# Some Files Modified Time Are The Same. Make Unique By Adding Now Time To Path
            if type=="Videos":prefix="VIDEO_"
            elif type=="Images":prefix="IMAGE_"
            basename=os.path.basename(path)
            text=os.path.splitext(basename)[0]
            if prefix in text:return path# File Already Renamed Before
            modified_time = os.path.getmtime(path)# Get File Modified Time
            mod_str=time.ctime(modified_time)
            mod_obj=time.strptime(mod_str)
            mod_time=time.strftime("%Y-%m-%d", mod_obj)
            mod_time=mod_time.replace(" ","_")
            now_time=str(perf_counter_ns())
            location=os.path.split(path)[0] + '/'
            file_name=prefix + mod_time +"_"+ now_time
            ext=str(os.path.splitext(path)[1])
            new_path=os.path.join(Path(location + file_name + ext.lower()))
            new_name=new_path.replace("\\","/")
            os.rename(path, new_name)
            return new_name
        except Exception:pass
        return None
    def rename_msg(self):
        msg1="Please Note: This Program Renames Video And Image Files!\n"
        msg2="The First Part Of The New Name Is The Original Creation\n"
        msg3="Date Followed By Present Timestamp. The Music Files Are\n"
        msg4="Not Renamed. If You Wish To Keep The Original File Names,\n"
        msg5="Unchanged, Please Make Copies And Point To The Copies!\n"
        msg6="You Can Also Keep The Original Names Intact By Renaming\n"
        msg7="Yourself With 'VIDEO_ Or IMAGE_' At The Beginning Of Name."
        msg=msg1+msg2+msg3+msg4+msg5+msg6+msg7
        messagebox.showinfo("<Renaming Video And Image Files>",msg)
    def find_in_folder(self,db):
        if db=='Music':
            exts=self.ffmpeg_audio_exts
            db_path=self.music_path
            music=True
        elif db=='Music_Favorite':
            exts=self.ffmpeg_audio_exts
            db_path=self.music_favorite_path
            music=True
        elif db=='Videos':
            exts=self.ffmpeg_video_exts
            db_path=self.video_path    
            music=False
        elif db=='Videos_Favorites':
            exts=self.ffmpeg_video_exts
            db_path=self.video_favorite_path  
            music=False
        elif db=='Videos_Karoake':
            exts=self.ffmpeg_video_exts
            db_path=self.video_karoake_path   
            music=False
        elif db=='Images':
            exts=self.ffmpeg_image_exts
            db_path=self.image_path    
            music=False
        elif db=='Images_Family':
            exts=self.ffmpeg_image_exts
            db_path=self.image_family_path   
            music=False
        elif db=='Images_Favorite':
            exts=self.ffmpeg_image_exts
            db_path=self.image_favorite_path
            music=False
        else:return
        if music==False:self.rename_msg()    
        folder_path=filedialog.askdirectory(title=f"Please Select A Folder To Upload To {db} Database.")  
        if folder_path=="" or folder_path==None:return
        temp_dict=json.load(open(db_path, "r+"))
        count=len(temp_dict)
        for root, _, files in os.walk(folder_path):
            if count>=1200:break
            try:
                for _, name in enumerate(files):
                    folder_path=os.path.join(root, name).replace("\\","/")
                    file_ext=os.path.splitext(name)[1].replace(".","")
                    file_path=folder_path[0].upper() + folder_path[1:]# Make Sure Drive Letter Always Capitalized
                    if file_ext.lower() in exts:
                        if music==False:# If Not Music File, Rename Files
                            file_path=self.rename_to_creation_date(file_path,db)
                            if file_path==None:continue
                        elif music==True:# If Music File, Check For Duplicates
                            if len(temp_dict)>=1:
                                if music==True:
                                    exist=self.check_duplicates(temp_dict, file_path)
                                    if exist:continue
                        temp_dict[count]=file_path
                        count+=1
                        if count>=1200:
                            msg1=f"Maximum Number Of 1200 {db} Has Been Reached.\n"
                            msg2="To Add More Files Please Select A Different Library!"
                            msg=msg1+msg2
                            messagebox.showinfo(f"<{db} Load Library>",msg)
                            break
            except Exception:continue
        with open(db_path, "w") as outfile:json.dump(temp_dict, outfile)
        outfile.close()
        temp_dict.clear()
        if self.active_database==db or self.active_database=="":self.load_library(db)
    def get_devices(self,capture_devices: bool = False):# False For Playback Devices, True For Capture
        mixer.init()# Only Use Pygame Mixer To Retrieve Audio Output Devices
        devices=[]
        output_devices=sdl2_audio.get_audio_device_names(capture_devices)
        mixer.quit()
        for d in output_devices:devices.append(d)
        return devices
    def destroy_widgets(self):# Destroys All Window Widgets
        try:
            for c in range(len(self.Media_Widgets)):
                self.Index_Widgets[c].destroy()
                self.Media_Widgets[c].destroy()
            self.parent.pack(side=LEFT, anchor=NW, fill=BOTH, expand=True, padx=(6,0), pady=(0,6))
            self.parent.canvas.update()
            self.Media_Dict.clear()
            self.Original_Dict.clear()
            self.Media_Widgets.clear()
            self.Index_Widgets.clear()
            root.update()
        except Exception:pass
    def write_setup(self):
        temp_dict={}
        sc=json.load(open(self.setup_path, "r"))
        json.dump(sc,open(self.setup_path, "w"),indent=4)
        temp_dict[0]=Screen_Height.get()
        temp_dict[1]=Screen_Position.get()
        temp_dict[2]=Slide_Show_Delay.get()
        with open(self.setup_path, "w") as outfile:json.dump(temp_dict, outfile)
        outfile.close()
        temp_dict.clear()
    def load_setup(self):
        temp_dict=json.load(open(self.setup_path, "r+"))
        if len(temp_dict)==0:
            hgt=int(screen_height-root_height)+int(0.2*taskbar_height)
            Screen_Height.set(hgt)
            Screen_Position.set("Top Center")
            temp_dict[0]=Screen_Height.get()
            temp_dict[1]=Screen_Position.get()
            if Slide_Show_Delay.get()=="":Slide_Show_Delay.set("0")
            temp_dict[2]=Slide_Show_Delay.get()
            with open(self.setup_path, "w") as outfile:json.dump(temp_dict, outfile)
            outfile.close()
            temp_dict.clear()
        else:    
            temp_dict[0]=Screen_Height.get()
            temp_dict[1]=Screen_Position.get()
            temp_dict[2]=Slide_Show_Delay.get()
            Screen_Height.set(temp_dict["0"])
            Screen_Position.set(temp_dict["1"])
            if Slide_Show_Delay.get()=="":Slide_Show_Delay.set("0")
            Slide_Show_Delay.set(temp_dict["2"])
    def load_library(self,db,skip=None):
        if skip==None:self.load_setup()
        if db=="Music":
            path=self.music_path
            self.active_media="music"
        elif db=="Music_Favorite":
            path=self.music_favorite_path
            self.active_media="music"
        elif db=="Videos":
            path=self.video_path
            self.active_media="video"
        elif db=="Videos_Favorite":
            path=self.video_favorite_path
            self.active_media="video"
        elif db=="Videos_Karoake":
            path=self.video_karoake_path
            self.active_media="video"
        elif db=="Images":
            path=self.image_path
            self.active_media="image"
        elif db=="Images_Family":
            path=self.image_family_path
            self.active_media="image"
        elif db=="Images_Favorite":
            path=self.image_favorite_path
            self.active_media="image"
        self.active_database=db
        self.destroy_widgets()
        self.Original_Dict=json.load(open(path, "r+"))
        self.Media_Dict=json.load(open(path, "r+"))
        if len(self.Media_Dict)==0:
            msg1=f'{self.active_database} Library Is Empty! Please Select\n'
            msg2='"Upload Folder Or File/s To Library" First.'
            msg=msg1+msg2
            messagebox.showwarning(f"<{self.active_database} Library>",msg)
            return
        root.title(f"My Media Player ({self.active_database} Library)")
        if self.shuffled and not self.repeat:
            temp=list(self.Media_Dict.values())
            random.shuffle(temp)
            self.Media_Dict=dict(zip(self.Media_Dict, temp))
        elif not self.shuffled:    
            temp=list(self.Original_Dict.values())
            self.Media_Dict=dict(zip(self.Original_Dict, temp))
        for key,self.file in self.Media_Dict.items():
            self.Index.append(int(key))
            self.Media_Btn.append(int(key))
            self.Index[int(key)]=Label(self.parent.media_window,text=str(int(key)+1)+".",relief="flat",
                        anchor='w',justify="left",background="#001829",foreground="#ffffff",font=media_font,)
            self.Index_Widgets[int(key)]=self.Index[int(key)]
            self.Index[int(key)].grid(row=int(key),column=0,columnspan=1,sticky=W)
            self.Media_Btn[int(key)]=Button(self.parent.media_window,name=str(int(key)),bg="#001829",fg="#ffffff", font=media_font,
                        anchor=NW,justify='center',relief='flat',border=None)
            self.Media_Btn[int(key)].bind("<ButtonRelease>",lambda event:self.ctrl_btn_clicked(event,"media play"))
            basename=os.path.basename(self.Media_Dict[key])
            text=os.path.splitext(basename)[0]
            self.Media_Btn[int(key)].configure(text=text,activebackground="#4cffff")
            self.Media_Widgets[int(key)]=self.Media_Btn[int(key)]
            self.Media_Btn[int(key)].grid(row=int(key),column=1,columnspan=1,sticky=W)
            if int(key)>1200:break 
        self.parent.media_window.update()
        self.parent.pack(side=LEFT,anchor=NW,fill=BOTH,expand=True,padx=(6,0),pady=(0,6))
        self.parent.canvas.xview_moveto(0)# Position Scrollbar To Position 0 For New Table
        self.parent.canvas.yview_moveto(0)
        self.parent.canvas.update()
    def select_output_device(self,device):
        try:
            devices=self.get_devices()# Quit Mixer
            result=list(filter(lambda x: device in x, devices))
            self.Active_Device=result[0]
            soundview_device=self.Active_Device.split("(", 1)[0].replace(" ","")
            cmd=[soundview_path, "/SetDefault", soundview_device, "1", "/Unmute", soundview_device, "/SetVolume", soundview_device, str(Level.get())]
            subprocess.run(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            devices=AudioUtilities.GetSpeakers()# Initialize Master Volumn Slider
            interface=devices.Activate(IAudioEndpointVolume._iid_, CLSCTX_ALL, None)
            self.Master_Volume=cast(interface, POINTER(IAudioEndpointVolume))
            Level.set(5)
            self.Master_Volume.SetMasterVolumeLevelScalar(Level.get()/100, None)
        except Exception as ex:
            title='<Audio Output Device>'
            msg1='Initialization Audio Device Failed. Ending Program!\n'
            msg2=f"Error: '{ex}'"
            msg3="Using Default Audio Device."
            messagebox.showerror(title, msg1+msg2+msg3)
            pass
def my_askinteger(title,prompt,init_val,min_val,max_val):
    d=My_IntegerDialog(title, prompt ,init_val,min_val,max_val)
    answer=d.result
    root.update_idletasks()
    return answer  
class My_IntegerDialog(tk.simpledialog._QueryInteger):
    def body(self, master):
        self.attributes("-toolwindow", True)# Remove Min/Max Buttons
        self.bind('<KP_Enter>', self.ok)
        self.bind('<Return>', self.ok)
        pt=tk.Label(master, text=self.prompt, justify="left", font=media_font)
        pad=int((pt.winfo_reqwidth()/2)/2)
        pt.grid(row=2, padx=(5,5),pady=(5,5), sticky=W+E)
        self.entry=tk.Entry(master, name="entry", justify='center', bg="#d6ffff", font=media_font)
        self.entry.grid(row=3, padx=(pad,pad), sticky=W+E)
        self.entry.bind('<Map>', self.on_map)
        if self.initialvalue is not None:
            self.entry.insert(0, self.initialvalue)
            self.entry.select_range(0, END)
        root.update_idletasks()
        return self.entry
    def on_map(self, event):
        self.entry.focus_force()    
def set_slide_show():
    title="<Set Slide Show Delay Time In Seconds>"
    msg1='Enter A Delay Time In Seconds For Image Slide Show.\n'
    msg2='A Delay Time Of 0 Seconds Indicates No Slide Show.\n'
    msg3='Maximum Delay Time Is 120 Seconds.'
    msg=msg1+msg2+msg3
    delay=my_askinteger(title,msg,int(Slide_Show_Delay.get()),0,120)
    if delay!=None:
        Slide_Show_Delay.set(str(delay))
        FF_Player.write_setup()
def set_screen_size():
    title="<Set Screen Size For Media Window>"
    default=str((screen_height-root_height)+int(0.2*taskbar_height))
    msg1='Enter A Screen Height For Video Playback.\n'
    msg2=f"Default Screen Height For This Monitor = {default}.\n"
    msg3='Maximum Height For This Monitor is ' + str(work_area[3]) +' (Full Screen).\n'
    msg4='The Screen Width Will Be Determined By This Monitors Aspect Ratio!'
    msg=msg1+msg2+msg3+msg4
    hgt=my_askinteger(title,msg,Screen_Height.get(),100,work_area[3])
    if hgt!=None:
        Screen_Height.set(hgt)
        FF_Player.write_setup()
def my_askstring(title, prompt, init_val=None):
    d=My_StringDialog(title, prompt , init_val)
    answer=d.result
    root.update_idletasks()
    return answer  
class My_StringDialog(tk.simpledialog._QueryString):
    def body(self, master):# initialvalue May Be List, String Or None
        self.attributes("-toolwindow", True)# Remove Min/Max Buttons
        self.bind('<KP_Enter>', self.ok)
        self.bind('<Return>', self.ok)
        pt=tk.Label(master, text=self.prompt, justify="left", font=media_font)
        pad=int((pt.winfo_reqwidth()/2)/2)
        pt.grid(row=2, padx=(5,5),pady=(5,5), sticky=W+E)
        if self.initialvalue is not None:
            if type(self.initialvalue)==list:# List
                self.entry=ttk.Combobox(master, name="entry", state = "readonly",justify="center",font=media_font)
                self.entry['values']=self.initialvalue
                index=self.initialvalue.index(Screen_Position.get())
                self.entry.current(index)
            else:# String
                self.entry=tk.Entry(master, name="entry", justify='center', bg="#d6ffff", font=media_font)
                self.entry.insert(0, self.initialvalue)
                self.entry.select_range(0, END)
        else:# None
            self.entry=tk.Entry(master, name="entry", justify='center', bg="#d6ffff", font=media_font)
            self.entry.insert(0, "")
            self.entry.select_range(0, END)
        self.entry.grid(row=3, padx=(pad,pad), sticky=W+E)
        self.entry.bind('<Map>', self.on_map)
        root.update_idletasks()
        return self.entry
    def on_map(self, event):
        self.entry.focus_force()    
def set_screen_position():
    title="<Set Screen Position For Media Window>"
    msg1='Select A Screen Position For Video Playback.\n'
    msg2='The Default Position Is ' + Screen_Position.get()+'.'
    msg=msg1+msg2
    positions=["Top Left","Top Center","Top Right","Center Left","Center","Center Right","Bottom Left","Bottom Center","Bottom Right"]
    pos=my_askstring(title,msg,positions)
    if pos!=None:
        Screen_Position.set(pos)
        FF_Player.write_setup()
class Media_Screen(tk.Frame):
    def __init__(self, parent):
        super().__init__(parent)
        self.config(bg="#094983",relief="flat",borderwidth=1)
        self.pack(padx=(0,0),pady=(0,0))
        wid=int(0.25*root_width)
        self.canvas=tk.Canvas(self,bg="#001829",width=wid)
        scrollstyle=ttk.Style()
        scrollstyle.theme_use('classic')
        self.vbar=ttk.Scrollbar(self,orient='vertical',command=self.canvas.yview)
        self.vbar.pack(side=RIGHT,fill=Y,padx=(0,0),pady=(0,0))                                        
        self.hbar=ttk.Scrollbar(self, orient="horizontal", command=self.canvas.xview)
        self.hbar.pack(side=BOTTOM,fill=X,padx=(0,0),pady=(0,0))
        self.canvas.pack(side=TOP, anchor=NW, fill=BOTH, expand=True, padx=(0,6), pady=(6,6))
        self.media_window=tk.Frame(self.canvas,bg="#001829")
        self.media_window.pack(side=TOP,anchor=NW,fill=BOTH, expand=True, padx=(6,6), pady=(6,6))                     
        self.canvas.configure(xscrollcommand=self.hbar.set,yscrollcommand=self.vbar.set)                          
        self.canvas_window=self.canvas.create_window((0,0),window=self.media_window,anchor=NW,tags="self.media_window") 
        self.canvas.update
        self.canvas.bind("<Key-Prior>", self.page_up)
        self.canvas.bind("<Key-Next>", self.page_down)
        self.canvas.bind("<Key-Up>", self.unit_up)
        self.canvas.bind("<Key-Down>", self.unit_down)        
        self.canvas.bind("<Key-Left>", self.unit_left)
        self.canvas.bind("<Key-Right>", self.unit_right)
        self.media_window.bind("<Configure>", self.rst_frame)                       
        self.media_window.bind('<Enter>', self.inside_canvas)                                 
        self.media_window.bind('<Leave>', self.outside_canvas)
        self.rst_frame(None)
    def rst_frame(self, event):                                              
        self.canvas.configure(scrollregion=self.canvas.bbox(ALL))                 
    def unit_up(self, event):
        self.canvas.yview_scroll(-1, "unit")
        return "break"
    def unit_down(self, event):
        self.canvas.yview_scroll(1, "unit")
        return "break"
    def unit_left(self, event):
        self.canvas.xview_scroll(-1, "unit")
        return "break"
    def unit_right(self, event):
        self.canvas.xview_scroll(1, "unit")
        return "break"
    def page_up(self, event):
        self.canvas.yview_scroll(-1, "page")
        return "break"
    def page_down(self, event):
        self.canvas.yview_scroll(1, "page")
        return "break"
    def scroll_mousey(self, event):
        self.canvas.yview_scroll(int(-1* (event.delta/120)), 'units')
    def inside_canvas(self, event):                                                       
        self.canvas.focus_set()                                                 
        self.canvas.bind_all("<MouseWheel>", self.scroll_mousey)
    def outside_canvas(self, event):                                                       
        self.canvas.unbind_all("<MouseWheel>")
def open_soundview():
    if os.path.isfile(soundview_path):
        root.withdraw()
        process=subprocess.Popen([soundview_path], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        process.wait()
        root.deiconify()
        root.grab_set()
        root.focus_force()
def about():
    msg1='Creator: Ross Waters\nEmail: RossWatersjr@gmail.com\nLanguage: Python version 3.12.2 64-bit\n'
    msg2='Revision: 3.8\nRevision Date: 06/27/2024\nCreated For Windows 11'
    msg=msg1+msg2
    messagebox.showinfo('My Media Player', msg)
def destroy(restart=None):
    try:
        FF_Player.destroy_widgets()
        for widget in root.winfo_children():# Destroys Menu Bars, Frame, Canvas And Scroll Bars
            if isinstance(widget, tk.Canvas):widget.destroy()
            else:widget.destroy()
        if restart!=None:
            os.execl(sys.executable, os.path.abspath(__file__), *sys.argv)
        FF_Player.process_ffplay.kill()
        os._exit(0)
    except Exception:
        pass
    os._exit(0)
if __name__ == '__main__':
    root=tk.Tk()
    style=ttk.Style()
    style.theme_use('classic')
    style.map('TCombobox', background=[('readonly','#0b5394')])# Down Arrow
    style.map('TCombobox', fieldbackground=[('readonly','#d4f2f2')])
    style.map('TCombobox', selectbackground=[('readonly','#0b5394')])
    style.map('TCombobox', selectforeground=[('readonly', '#ffffff')])
    primary_monitor=MonitorFromPoint((0, 0))
    monitor_info=GetMonitorInfo(primary_monitor)
    monitor_area=monitor_info.get("Monitor")
    work_area=monitor_info.get("Work")
    aspect_ratio=work_area[2]/work_area[3]
    taskbar_height=monitor_area[3]-work_area[3]
    screen_height=work_area[3]-taskbar_height
    root_width=int(work_area[2]*0.8)
    root.wm_attributes("-topmost",True)
    root.configure(bg="#094983")
    ico_path=os.path.join(Path(__file__).parent.absolute(),"movie.ico")
    root.iconbitmap(default=ico_path)# root and children
    root.title("My Media Player")
    root.resizable(True,True)
    button_font=font.Font(family='Times New Romans', size=9, weight='bold', slant='italic')
    media_font=font.Font(family='Times New Romans', size=9, weight='normal', slant='italic')
    root.protocol("WM_DELETE_WINDOW", destroy)
    ffmpeg_path=os.path.join(Path(__file__).parent.absolute(), "ffmpeg.exe")
    soundview_path=os.path.join(Path(__file__).parent.absolute(), "SoundVolumeView.exe")
    Start_Time=DoubleVar()
    Paused=BooleanVar()
    Level=DoubleVar()# Volume Meter
    Bluetooth_State=BooleanVar()
    Screen_Height=IntVar()
    Screen_Position=StringVar()
    Slide_Show_Delay=StringVar()
    Media_Scroll=Media_Screen(root) # Vertical/Horizontal Scrollbar Window
    Media_Scroll.pack(side=LEFT, anchor=NW, fill=BOTH, expand=False, padx=(10,0), pady=(0,12))
    FF_Player=FFPLAY(Media_Scroll)
    FF_Player.initialize()
    pgm_Path=Path(__file__).parent.absolute()
    title_skin=tk.PhotoImage(file=os.path.join(pgm_Path, '1280x40.png'))
    btn_skin=tk.PhotoImage(file=os.path.join(pgm_Path, '400x40.png'))
    main_frame=tk.Frame(root,relief="raised",borderwidth=5)
    main_frame.pack(side=TOP,anchor=NW,fill=X, expand=False, padx=(0,0), pady=(0,0))
    main_frame.config(bg="#0b5394")
    title_frame=tk.Frame(main_frame,relief="sunken",borderwidth=3)
    title_frame.pack(side=TOP,anchor=NW,fill=X, expand=True, padx=(3,3), pady=(3,3))
    title_frame.config(bg="#000000")
    pix_wid=int(root_width*0.17) #Make Width 17% Of Root Width Using Label image=tk.PhotoImage(),Zero Image 
    volume_lbl=tk.Button(title_frame,text='Master Volume',image=btn_skin, compound="center",width=pix_wid-5,height=20,
                background="#bcbcbc",foreground="#000000",font=button_font,justify="center",relief='sunken',borderwidth=5)
    volume_lbl.pack(side=LEFT,anchor=NW,fill=BOTH, expand=False, padx=(3,0), pady=(3,3))
    title_lbl=tk.Button(title_frame,text="",image=title_skin, compound="center",height=20,
                    background="#aeaeae",foreground="#000000",font=button_font,justify="center",relief='sunken',borderwidth=5)
    title_lbl.pack(side=RIGHT,anchor=NE,fill=BOTH,expand=True,padx=(5,3), pady=(3,3))
    slider_frame=tk.Frame(main_frame,relief="sunken",borderwidth=3)
    slider_frame.pack(side=TOP,anchor=NW,fill=BOTH, expand=False, padx=(3,3), pady=(0,3))
    slider_frame.config(bg="#000000")
    volume=tk.Scale(slider_frame, variable=Level, from_=0,to=100, orient='horizontal', resolution=1, 
                    tickinterval=50,showvalue=1,borderwidth=5,relief="sunken",font=button_font,
                    length=pix_wid,bg="#aeaeae",fg="#000000",troughcolor="#001829", activebackground="#0061aa",
                    highlightthickness=0,command=lambda event:FF_Player.set_master_volume())
    volume.pack(side=LEFT,anchor=NW,fill=BOTH, expand=False, padx=(3,0), pady=(3,3))
    volume.bind("<ButtonRelease-1>",lambda event:FF_Player.slider_released())# Sets Video Window Active
    time_scale=tk.Scale(slider_frame, relief="sunken",orient='horizontal',resolution=0,
                        bg="#aeaeae",borderwidth=5,font=button_font,fg="#000000",troughcolor="#001829",  
                        activebackground="#0061aa",highlightthickness=0)
    time_scale.pack(side=LEFT,anchor=NW,fill=BOTH,expand=True, padx=(5,3), pady=(3,3))
    time_scale.bind("<ButtonRelease-1>",lambda event:FF_Player.end_seeking(event))
    time_scale.bind("<ButtonPress-1>",lambda event:FF_Player.begin_seeking(event))
    ctrl_frame=tk.Frame(main_frame,relief="sunken",borderwidth=3)
    ctrl_frame.pack(side=RIGHT,anchor=NE,fill=BOTH, expand=True, padx=(3,3), pady=(0,3))
    ctrl_frame.config(bg="#000000")
    quit_btn=tk.Button(ctrl_frame,text="Quit",foreground="#000000",image=btn_skin, compound="center",font=button_font,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",width=1,height=20)
    quit_btn.pack(side=RIGHT,fill=X, expand=True, padx=(5,3), pady=(3,3))
    quit_btn.bind("<ButtonRelease>",lambda event:FF_Player.quit(event))
    stop_btn=tk.Button(ctrl_frame,text="Stop",foreground="#000000",image=btn_skin, compound="center",font=button_font,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",width=1,height=20)
    stop_btn.pack(side=RIGHT,fill=X, expand=True, padx=(0,0), pady=(3,3))
    stop_btn.bind("<ButtonRelease>",lambda event:FF_Player.ctrl_btn_clicked(event,"stop"))
    mute_btn=tk.Button(ctrl_frame,text="Mute",foreground="#000000",image=btn_skin, compound="center",font=button_font,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",width=1,height=20)
    mute_btn.pack(side=RIGHT,fill=X, expand=True, padx=(5,5), pady=(3,3))
    mute_btn.bind("<ButtonRelease>",lambda event:FF_Player.ctrl_btn_clicked(event,"mute"))
    repeat_btn=tk.Button(ctrl_frame,text="Repeat",foreground="#000000",image=btn_skin, compound="center",font=button_font,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",width=1,height=20)
    repeat_btn.pack(side=RIGHT,fill=X, expand=True, padx=(0,0), pady=(3,3))
    repeat_btn.bind("<ButtonRelease>",lambda event:FF_Player.ctrl_btn_clicked(event,"repeat"))
    pause_btn=tk.Button(ctrl_frame,text="Pause",foreground="#000000",image=btn_skin, compound="center",font=button_font,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",width=1,height=20)
    pause_btn.pack(side=RIGHT,fill=X, expand=True, padx=(5,5), pady=(3,3))
    pause_btn.bind("<ButtonRelease>",lambda event:FF_Player.pause(event))
    next_btn=tk.Button(ctrl_frame,text="Next",foreground="#000000",image=btn_skin, compound="center",font=button_font,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",width=1,height=20)
    next_btn.pack(side=RIGHT,fill=X, expand=True, padx=(0,0), pady=(3,3))
    next_btn.bind("<ButtonRelease>",lambda event:FF_Player.ctrl_btn_clicked(event,"next"))
    previous_btn=tk.Button(ctrl_frame,text="Previous",foreground="#000000",image=btn_skin, compound="center",font=button_font,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",width=1,height=20)
    previous_btn.pack(side=RIGHT,fill=X, expand=True, padx=(5,5), pady=(3,3))
    previous_btn.bind("<ButtonRelease>",lambda event:FF_Player.ctrl_btn_clicked(event,"previous"))
    shuffle_btn=tk.Button(ctrl_frame,text="Shuffle Play",foreground="#000000",image=btn_skin, compound="center",font=button_font,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",width=1,height=20)
    shuffle_btn.pack(side=RIGHT,fill=X, expand=True, padx=(0,0), pady=(3,3))
    shuffle_btn.bind("<ButtonRelease>",lambda event:FF_Player.ctrl_btn_clicked(event,"shuffled"))
    play_btn=tk.Button(ctrl_frame,text="Play",foreground="#000000",image=btn_skin, compound="center",font=button_font,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",width=1,height=20)
    play_btn.pack(side=RIGHT,fill=X, expand=True, padx=(3,5), pady=(3,3))
    play_btn.bind("<ButtonRelease>",lambda event:FF_Player.ctrl_btn_clicked(event,"btn play"))
    FF_Player.load_menubar()
    root.update()
    root_height=main_frame.winfo_reqheight()
    x=(work_area[2]/2)-(root_width/2)
    root_x=int(x-((7/x)*x))# x Not Exactly Centered, Use Correction Factor
    root_y=screen_height-root_height
    root.geometry('%dx%d+%d+%d' % (root_width, root_height, root_x, root_y, ))
    root.update()
    root.after(500, FF_Player.load_library("Music"))    
    root.mainloop()

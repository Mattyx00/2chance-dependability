package controller;

import model.beans.Utente;
import model.dao.UtenteDAO;
import utils.LoginErratoException;

import javax.servlet.*;
import javax.servlet.http.*;
import javax.servlet.annotation.*;
import java.io.IOException;
import java.sql.SQLDataException;
import java.sql.SQLException;
import java.util.ArrayList;

@WebServlet(name = "LoginServlet", value = "/LoginServlet")
public class LoginServlet extends HttpServlet {
    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        String email = request.getParameter("email");
        String password = request.getParameter("password");

        ArrayList<String> errori = new ArrayList<>();

        try {
            UtenteDAO dao = new UtenteDAO();
            Utente utente = dao.getUserByEmailPassword(email, password);
            if(utente == null){
                throw new LoginErratoException();
            }

            HttpSession session = request.getSession();
            session.setAttribute("user", utente);

            if(utente.isAdmin()){
                response.sendRedirect(request.getServletContext().getContextPath()+"/dashboard.jsp");
            }
            else
                response.sendRedirect( request.getServletContext().getContextPath()+"/landingpage");


        } catch (SQLException e) {
           response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
        }
        catch(LoginErratoException e2){
            errori.add("Email o password errati");
            request.setAttribute("errori", errori);
            request.setAttribute("email", email);
            String address = "/login.jsp";
            RequestDispatcher dispatcher = request.getRequestDispatcher(address);
            dispatcher.forward(request, response);
        }


    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        doGet(request, response);
    }
}

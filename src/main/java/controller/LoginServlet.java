package controller;

import model.beans.Utente;
import services.LoginService;
import utils.LoginErratoException;

import javax.servlet.RequestDispatcher;
import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.HttpSession;
import java.io.IOException;
import java.sql.SQLException;
import java.util.ArrayList;

@WebServlet(name = "LoginServlet", value = "/LoginServlet")
public class LoginServlet extends HttpServlet {
    private LoginService loginService;

    @Override
    public void init() throws ServletException {
        try {
            this.loginService = new LoginService();
        } catch (SQLException e) {
            throw new ServletException("Failed to initialize LoginService", e);
        }
    }

    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {
        try {
            String email = request.getParameter("email");
            String password = request.getParameter("password");

            ArrayList<String> errori = new ArrayList<>();

            try {
                Utente utente = loginService.login(email, password);

                HttpSession session = request.getSession();
                session.setAttribute("user", utente);

                if (utente.isAdmin()) {
                    response.sendRedirect(request.getServletContext().getContextPath() + "/dashboard.jsp");
                } else {
                    response.sendRedirect(request.getServletContext().getContextPath() + "/landingpage");
                }

            } catch (SQLException e) {
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
            } catch (LoginErratoException e2) {
                errori.add("Email o password errati");
                request.setAttribute("errori", errori);
                request.setAttribute("email", email);
                String address = "/login.jsp";
                RequestDispatcher dispatcher = request.getRequestDispatcher(address);
                dispatcher.forward(request, response);
            }
        } catch (Exception e) {
            e.printStackTrace();
            if (!response.isCommitted()) {
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
            }
        }
    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {
        try {
            doGet(request, response);
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}
